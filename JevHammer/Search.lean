module

public meta import JevHammer.Types
public meta import JevHammer.DefaultTactics
public meta import JevHammer.Premises

public meta section
namespace JevHammer
open Lean Meta Elab

initialize registerTraceClass `JevHammer

private def goalView (g : MVarId) : MetaM Json := g.withContext do
  withOptions (·.setBool `pp.mvars false) do
    let mut context := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        let value ← match d.value? with
          | some v => pure (toJson (← ppExpr (← instantiateMVars v)).pretty)
          | none => pure Json.null
        context := context.push <| Json.mkObj [("name", toJson d.userName.toString),
          ("type", toJson (← ppExpr (← instantiateMVars d.type)).pretty), ("value", value)]
    return Json.mkObj [("target", toJson (← ppExpr (← instantiateMVars (← g.getType))).pretty),
      ("context", .arr context)]

private structure Runtime where
  config : Config
  ranker : Ranker
  stats : IO.Ref Stats
  start : Nat
  selector : LibrarySuggestions.Selector
  tactics : TacticSet

private def Runtime.check (rt : Runtime) : MetaM Unit := do
  if (← IO.monoMsNow) - rt.start >= rt.config.maxMillis then
    rt.stats.modify fun s => { s with exhausted := true }
    throwError "JevHammer wall budget exhausted"

private def Runtime.rank (rt : Runtime) (state : Json) (choices : Array Json) : MetaM (Array Nat) := do
  let fallback := (List.range choices.size).toArray
  if choices.size < 2 then return fallback
  if (← rt.stats.get).rankCalls >= rt.config.maxCalls then return fallback
  rt.check
  let isState := state.getObjValD "task" == .str "continuations"
  rt.stats.modify fun s => { s with
    rankCalls := s.rankCalls + 1,
    premiseRankCalls := s.premiseRankCalls + if isState then 0 else 1,
    selectorRankCalls := s.selectorRankCalls +
      if state.getObjValD "task" == .str "selector" then 1 else 0,
    stateRankCalls := s.stateRankCalls + if isState then 1 else 0 }
  try
    let r ← rt.ranker state choices
    unless isPermutation r.order choices.size do throwError "invalid Jev ranking"
    rt.stats.modify fun s => { s with
      inputTokens := s.inputTokens + r.usage.inputTokens.getD 0
      outputTokens := s.outputTokens + r.usage.outputTokens.getD 0
      model := r.model }
    return r.order
  catch error =>
    rt.stats.modify fun s => { s with rankFailures := s.rankFailures + 1 }
    trace[JevHammer] "Jev ranking failed; keeping candidate order: {error.toMessageData}"
    return fallback

/-- Selectors cannot relabel their requests as proof-state work. They receive
the same budget/failure handling as the search, without direct client access. -/
private def Runtime.selectorRank (rt : Runtime) : SelectorRanker := fun question goal choices => do
  let fallback := (List.range choices.size).toArray
  if choices.size < 2 then return fallback
  if question.isEmpty then throwError "selector ranking needs a mathematical question"
  if (← rt.stats.get).rankCalls >= rt.config.maxCalls then return fallback
  rt.check
  let saved ← saveState
  try
    let state := Json.mkObj [("task", .str "selector"),
      ("independent_scores", .bool true), ("selector_question", toJson question),
      ("goal", ← goalView goal)]
    rt.rank state choices
  finally saved.restore

private def Runtime.tryCode (rt : Runtime) (g : MVarId) (code : String)
    (close : Bool := false) : MetaM (Option (List MVarId)) := do
  let _ : MonadExceptOf Exception MetaM :=
    { (inferInstance : MonadExceptOf Exception MetaM) with tryCatch := tryCatchRuntimeEx }
  rt.check
  let saved ← saveState
  rt.stats.modify fun s => { s with trials := s.trials + 1 }
  try
    let gs ← runCode g code rt.config.tacticHeartbeats
    if close && !gs.isEmpty then
      saved.restore
      return none
    return some gs
  catch _ =>
    saved.restore
    return none

/-- Generation is a query, never a committed proof step. In particular a custom
callback cannot leak assignments or declarations into the candidates it returns. -/
private def Runtime.generate (rt : Runtime) (generator : TacticGenerator)
    (g : MVarId) (premises : Array Name) : MetaM (Array String) := g.withContext do
  rt.check
  let saved ← saveState
  try
    withHeartbeatBudget rt.config.tacticHeartbeats <|
      generator { goal := g, premises, config := rt.config }
  finally saved.restore

private def closeWith (rt : Runtime) (generator : TacticGenerator)
    (g : MVarId) (premises : Array Name) : MetaM Bool := do
  for code in ← rt.generate generator g premises do
    if (← rt.tryCode g code true).isSome then
      rt.stats.modify fun s => { s with winner := code }
      return true
  return false

private def discharge (rt : Runtime) (g : MVarId)
    (premises : Array Name := #[]) : MetaM Bool :=
  closeWith rt rt.tactics.close g premises

private def prepare (rt : Runtime) (g : MVarId) : MetaM (List MVarId) := do
  let mut pending := [g]
  for code in ← rt.generate rt.tactics.prepare g #[] do
    let mut next := []
    for h in pending do
      unless ← h.isAssigned do
        match ← rt.tryCode h code with
        | none => next := next ++ [h]
        | some goals =>
          next := next ++ goals
          if goals.isEmpty then rt.stats.modify fun s => { s with winner := code }
    pending := next
    if pending.isEmpty then break
  return pending

private def premiseViews (names : Array Name) : MetaM (Array Json) := names.mapM fun n => do
  return Json.mkObj [("lemma", toJson n.toString), ("type", toJson (← ppExpr (← getConstInfo n).type).pretty)]

private def rankPremises (rt : Runtime) (g : MVarId) (previous : Array Name := #[]) : MetaM (Array Name) := g.withContext do
  let start ← IO.monoMsNow
  let names ← selectPremises rt.selector g rt.config.maxPremises
  let elapsed := (← IO.monoMsNow) - start
  rt.stats.modify fun s => { s with
    premises := s.premises + names.size
    retrievalMs := s.retrievalMs + elapsed }
  unless rt.config.guidePremises do return names
  let choices ← premiseViews names
  let goal ← goalView g
  let oldViews ← premiseViews previous
  let state := if previous.isEmpty then
    Json.mkObj [("task", .str "premises"), ("independent_scores", .bool true),
      ("goal", goal)]
    else Json.mkObj [("task", .str "premise_refresh"), ("independent_scores", .bool true),
      ("previous_premises", .arr oldViews),
      ("goal", goal)]
  let order ← rt.rank state choices
  return order.filterMap (names[·]?)

private def premiseFinish (rt : Runtime) (g : MVarId) (names : Array Name) : MetaM Bool :=
  closeWith rt rt.tactics.finish g names

private structure Branch where
  goals : List MVarId
  saved : Meta.SavedState
  path : Array String
  view : Json
  ancestors : Array String := #[]

private def branchView (gs : List MVarId) (path : Array String) : MetaM Json := do
  return Json.mkObj [("actions", toJson path), ("remaining", toJson (← gs.toArray.mapM goalView))]

private def expand (rt : Runtime) (b : Branch) (premises : Array Name) : MetaM (Array Branch) := do
  b.saved.restore
  let gs ← b.goals.filterM fun g => return !(← g.isAssigned)
  let g :: rest := gs | return #[b]
  let codes ← rt.generate rt.tactics.steps g premises
  let mut branches : Array Branch := #[]
  let mut seen : Array String := #[]
  for code in codes do
    if branches.size >= rt.config.maxCandidates then break
    b.saved.restore
    if let some next ← rt.tryCode g code then
      -- Close obvious subgoals before asking the model; assignments remain in the
      -- same snapshot as every sibling, including shared existential witnesses.
      let mut pending : List MVarId := []
      for h in next ++ rest do
        unless ← h.isAssigned do
          unless ← closeWith rt rt.tactics.cleanup h premises do
            pending := pending ++ [h]
      let path := b.path.push code
      let view ← branchView pending path
      let key := (view.getObjValD "remaining").compress
      if key == (b.view.getObjValD "remaining").compress || b.ancestors.contains key then continue
      if seen.contains key then continue
      seen := seen.push key
      branches := branches.push {
        goals := pending, saved := ← saveState, path, view,
        ancestors := b.ancestors.push (b.view.getObjValD "remaining").compress }
      if pending.isEmpty then break
  rt.stats.modify fun s => { s with branches := s.branches + branches.size }
  b.saved.restore
  return branches

private def lookahead (rt : Runtime) (g : MVarId) (premises : Array Name) : MetaM Bool := do
  let initial : Branch := { goals := [g], saved := ← saveState, path := #[], view := ← branchView [g] #[] }
  let mut frontier := #[initial]
  for _ in [:rt.config.maxDepth] do
    let mut successors : Array Branch := #[]
    for b in frontier do
      if (← rt.stats.get).nodes >= rt.config.maxNodes then
        rt.stats.modify fun s => { s with exhausted := true }
        return false
      rt.stats.modify fun s => { s with nodes := s.nodes + 1 }
      b.saved.restore
      if !b.path.isEmpty then
        let mut allClosed := true
        for h in b.goals do
          unless ← h.isAssigned do
            unless ← discharge rt h premises do
              allClosed := false
              break
        if allClosed then
          rt.stats.modify fun s => { s with winner := String.intercalate "; " b.path.toList ++ "; portfolio" }
          return true
      -- Failed closures must not leave a partially solved branch committed.
      b.saved.restore
      let mut branchPremises := premises
      if rt.config.refreshPremises && !b.path.isEmpty &&
          (← rt.stats.get).refreshes == 0 && (← rt.stats.get).rankCalls < rt.config.maxCalls then
        if let some h := b.goals.head? then
          rt.stats.modify fun s => { s with refreshes := s.refreshes + 1 }
          branchPremises ← rankPremises rt h premises
          if ← premiseFinish rt h branchPremises then
            let mut allClosed := true
            for other in b.goals do
              unless ← other.isAssigned do
                unless ← discharge rt other branchPremises do allClosed := false; break
            if allClosed then return true
          b.saved.restore
      let next ← expand rt b branchPremises
      for c in next do
        if c.goals.isEmpty then
          c.saved.restore
          rt.stats.modify fun s => { s with winner := String.intercalate "; " c.path.toList }
          return true
      successors := successors ++ next
    if successors.isEmpty then return false
    let state := [("task", .str "continuations"), ("goal", initial.view)]
    let order ← rt.rank (Json.mkObj state)
      (successors.map (·.view))
    let selected := order.take rt.config.beamWidth
    frontier := selected.filterMap (successors[·]?)
  -- Discharge the last selected layer, too.
  for b in frontier do
    if (← rt.stats.get).nodes >= rt.config.maxNodes then
      rt.stats.modify fun s => { s with exhausted := true }
      return false
    rt.stats.modify fun s => { s with nodes := s.nodes + 1 }
    b.saved.restore
    let mut ok := true
    for h in b.goals do
      unless ← h.isAssigned do
        unless ← discharge rt h premises do
          ok := false
          break
    if ok then
      rt.stats.modify fun s => { s with winner := String.intercalate "; " b.path.toList ++ "; portfolio" }
      return true
  return false
/-- Close the whole goal list with kernel-checked proofs, or restore its original
state. Supply any Lean premise selector, a Jev ranker (or an offline test ranker),
and optionally a complete tactic collection. The selector never has to depend
on this library. -/
def solve (goals : List MVarId) (selector : LibrarySuggestions.Selector)
    (ranker : Ranker) (stats : IO.Ref Stats) (config : Config := {})
    (tactics : TacticSet := defaultTactics)
    (selectorFactory : Option SelectorFactory := none) : MetaM Unit := do
  let _ : MonadExceptOf Exception MetaM :=
    { (inferInstance : MonadExceptOf Exception MetaM) with tryCatch := tryCatchRuntimeEx }
  let initial ← saveState
  let original ← getEnv
  let start ← IO.monoMsNow
  let rt : Runtime := { config, ranker, stats, start, selector, tactics }
  let rt := match selectorFactory with
    | none => rt
    | some make => { rt with selector := make rt.selectorRank selector }
  try
    for g in goals do
      if ← g.isAssigned then continue
      g.withContext do
        unless ← discharge rt g do
          for h in ← prepare rt g do
            unless ← h.isAssigned do
              h.withContext do
                let before ← saveState
                let premises ← rankPremises rt h
                unless ← premiseFinish rt h premises do
                  before.restore
                  unless ← lookahead rt h premises do throwError "JevHammer did not close the goals"
    for g in goals do
      g.withContext do
        let proof ← instantiateMVars (.mvar g)
        unless ← isDefEq (← inferType proof) (← g.getType) do
          throwError "JevHammer produced a proof of the wrong type"
        let closed ← kernelCheckClosure proof
        let replayable ← inlineAuxiliaries original closed
        discard <| withEnv original <| kernelCheckClosure replayable
  catch error =>
    initial.restore
    throw error
  finally
    let elapsed := (← IO.monoMsNow) - start
    stats.modify fun s => { s with elapsedMs := elapsed }

end JevHammer
