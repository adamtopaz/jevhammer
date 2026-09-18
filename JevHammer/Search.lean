module

public meta import JevHammer.Types
public meta import JevHammer.Proof
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

private def discharge (rt : Runtime) (g : MVarId) : MetaM Bool := do
  for code in portfolioCodes do
    if (← rt.tryCode g code true).isSome then
      rt.stats.modify fun s => { s with winner := code }
      return true
  return false

private def relevantSymbol (n : Name) : Bool :=
  !([``Eq, ``Iff, ``And, ``Or, ``Not, ``Exists, ``True, ``False, ``Decidable,
     ``OfNat.ofNat, ``OfNat, ``Nat, ``Int].contains n) &&
  !n.isInternal && !n.toString.startsWith "Lean." && !n.toString.startsWith "JevPilot."

/-- Round-robin selection prevents one retrieval or action route from filling the cap. -/
def interleaveUnique (routes : Array (Array String)) (limit : Nat) : Array String := Id.run do
  let mut result := #[]
  let depth := routes.foldl (fun n r => max n r.size) 0
  for i in [:depth] do
    for route in routes do
      if result.size >= limit then return result
      if let some item := route[i]? then
        unless result.contains item do result := result.push item
  return result

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

private def premiseFinish (rt : Runtime) (g : MVarId) (names : Array Name) : MetaM Bool := do
  for count in #[rt.config.premiseCount, rt.config.premiseCount * 2] do
    let ns := names.take count
    unless ns.isEmpty do
      let printed ← ns.mapM fun name => return (← unresolveNameGlobal name).toString
      let args := String.intercalate ", " printed.toList
      for code in #[s!"solve | simp_all [{args}]", s!"grind (gen := 8) [{args}]",
          s!"aesop (add unsafe 50% {String.intercalate " " printed.toList})" ++ " (config := { maxRuleApplications := 160 })"] do
        if (← rt.tryCode g code true).isSome then
          rt.stats.modify fun s => { s with winner := code }
          return true
  return false

private structure Branch where
  goals : List MVarId
  saved : Meta.SavedState
  path : Array String
  view : Json
  ancestors : Array String := #[]

private def branchView (gs : List MVarId) (path : Array String) : MetaM Json := do
  return Json.mkObj [("actions", toJson path), ("remaining", toJson (← gs.toArray.mapM goalView))]

private def actionCodes (g : MVarId) (premises : Array Name) : MetaM (Array String) := g.withContext do
  let mut codes := #["simp_all", "intros", "constructor", "ext1", "contrapose!", "push_neg at *", "symm"]
  let basic := codes
  let mut definitions := #[]
  let mut localApply := #[]
  let mut localCases := #[]
  let mut localRewrite := #[]
  let mut lemmaApply := #[]
  let mut lemmaRewrite := #[]
  let mut lemmaSimp := #[]
  -- Selective definitional normalization is generated from expressions, not a
  -- hand-maintained list of mathematics-specific rewrite rules.
  let symbols := (← instantiateMVars (← g.getType)).getUsedConstants.filter relevantSymbol
  for n in symbols.take 8 do
    if (← getConstInfo n).isDefinition then
      let more := #[s!"unfold {n}", s!"simp_all only [{n}]"]
      codes := codes ++ more
      definitions := definitions ++ more
  let mut hypCount := 0
  for h in ← getLCtx do
    if h.isImplementationDetail || h.userName.isInternal || hypCount >= 8 then continue
    if ← isProp h.type then
      let id := h.userName.toString
      codes := codes ++ #[s!"apply {id}", s!"cases {id}", s!"rw [{id}]", s!"rw [← {id}]"]
      localApply := localApply.push s!"apply {id}"
      localCases := localCases.push s!"cases {id}"
      localRewrite := localRewrite ++ #[s!"rw [{id}]", s!"rw [← {id}]"]
      hypCount := hypCount + 1
  for n in premises.take 12 do
    let n := (← unresolveNameGlobal n).toString
    codes := codes ++ #[s!"apply {n}", s!"rw [{n}]", s!"rw [← {n}]", s!"simp only [{n}] at *"]
    lemmaApply := lemmaApply.push s!"apply {n}"
    lemmaRewrite := lemmaRewrite ++ #[s!"rw [{n}]", s!"rw [← {n}]"]
    lemmaSimp := lemmaSimp.push s!"simp only [{n}] at *"
  return interleaveUnique #[basic, lemmaApply, localApply, lemmaRewrite, definitions,
    localCases, lemmaSimp, localRewrite] codes.size

private def expand (rt : Runtime) (b : Branch) (premises : Array Name) : MetaM (Array Branch) := do
  b.saved.restore
  let gs ← b.goals.filterM fun g => return !(← g.isAssigned)
  let g :: rest := gs | return #[b]
  let codes ← actionCodes g premises
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
          if (← rt.tryCode h "solve | assumption | rfl | trivial" true).isNone then
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
            unless ← discharge rt h do
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
                unless ← discharge rt other do allClosed := false; break
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
        unless ← discharge rt h do
          ok := false
          break
    if ok then
      rt.stats.modify fun s => { s with winner := String.intercalate "; " b.path.toList ++ "; portfolio" }
      return true
  return false
/-- Close the whole goal list with kernel-checked proofs, or restore its original
state. Supply any Lean premise selector and a Jev ranker (or an offline test
ranker). The selector never has to depend on this library. -/
def solve (goals : List MVarId) (selector : LibrarySuggestions.Selector)
    (ranker : Ranker) (stats : IO.Ref Stats) (config : Config := {}) : MetaM Unit := do
  let _ : MonadExceptOf Exception MetaM :=
    { (inferInstance : MonadExceptOf Exception MetaM) with tryCatch := tryCatchRuntimeEx }
  let initial ← saveState
  let original ← getEnv
  let start ← IO.monoMsNow
  let rt : Runtime := { config, ranker, stats, start, selector }
  try
    for g in goals do
      if ← g.isAssigned then continue
      g.withContext do
        unless ← discharge rt g do
          let (_, g) ← g.intros
          let before ← saveState
          let premises ← rankPremises rt g
          unless ← premiseFinish rt g premises do
            before.restore
            unless ← lookahead rt g premises do throwError "JevHammer did not close the goals"
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
