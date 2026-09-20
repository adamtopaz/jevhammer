import JevHammerTests.Regression

open Lean Meta Elab Tactic LibrarySuggestions JevHammer
set_option Elab.async false
set_option maxHeartbeats 4000000

namespace JevHammerTests.DeferredGuidance

private def trueSelector : Selector := fun _ cfg => pure <| #[
  { name := ``True.intro, score := 1 }, { name := ``And.intro, score := 0.5 }].take cfg.maxSuggestions

private def trueTactics : TacticSet := {
  finish := fun ctx => pure <| if ctx.premises.contains ``True.intro then
    #["exact True.intro"] else #[] }

private def forbidden : SelectorFactory := fun _ _ _ _ =>
  throwError "CPU premise finishing must not invoke the factory"

-- These need no credentials even though the ordinary cheap prefix is empty.
example : True := by
  jev_hammer (deferPremiseGuidance := true) with trueTactics using trueSelector guiding forbidden

elab "check_deferred_guidance_skip" : tactic => withMainContext do
  for defer in #[false, true] do
    for ordinaryReranking in #[false, true] do
      let goal ← mkFreshExprMVar (mkConst ``True)
      let calls ← IO.mkRef (0 : Nat)
      let queries ← IO.mkRef (0 : Nat)
      let factoryCalls ← IO.mkRef (0 : Nat)
      let base : Selector := fun g cfg => do
        queries.modify (· + 1)
        trueSelector g cfg
      let factory : SelectorFactory := fun rank base g cfg => do
        factoryCalls.modify (· + 1)
        discard <| rank "Will this premise set finish the goal?" g #[.str "first", .str "second"]
        base g cfg
      let ranker : Ranker := fun _ cs => do
        calls.modify (· + 1)
        pure { order := (List.range cs.size).toArray }
      let stats ← IO.mkRef ({} : Stats)
      solve [goal.mvarId!] base ranker stats {
        maxMillis := 30000, deferPremiseGuidance := defer, guidePremises := ordinaryReranking }
        trueTactics (if ordinaryReranking then none else some factory)
      let s ← stats.get
      unless (← goal.mvarId!.isAssigned) && (← queries.get) == 1 &&
          (← calls.get) == (if defer then 0 else 1) &&
          (← factoryCalls.get) == (if defer || ordinaryReranking then 0 else 1) &&
          s.rankCalls == (if defer then 0 else 1) &&
          s.unguidedPremiseAttempts == (if defer then 1 else 0) &&
          s.unguidedPremiseFinishes == s.unguidedPremiseAttempts do
        throwError "early premise finishing did not skip guidance or changed the default path"
  let goal ← mkFreshExprMVar (mkConst ``True)
  let queries ← IO.mkRef (0 : Nat)
  let base : Selector := fun g cfg => do queries.modify (· + 1); trueSelector g cfg
  let stats ← IO.mkRef ({} : Stats)
  solve [goal.mvarId!] base (fun _ _ => throw <| IO.userError "unguided method called model")
    stats { maxMillis := 30000, deferPremiseGuidance := true } trueTactics
  unless (← queries.get) == 1 && (← stats.get).unguidedPremiseAttempts == 0 do
    throwError "a method without premise guidance acquired an extra finishing pass"

example : True := by check_deferred_guidance_skip; trivial

elab "check_deferred_guidance_fallback" : tactic => withMainContext do
  let target := mkApp2 (mkConst ``And) (mkConst ``True) (mkConst ``True)
  let goal ← mkFreshExprMVar target
  let queries ← IO.mkRef (0 : Nat)
  let base : Selector := fun g _ => do
    if ← g.isAssigned then throwError "failed early finishing leaked a goal assignment"
    queries.modify (· + 1)
    pure #[]
  let factory : SelectorFactory := fun rank base g cfg => do
    if ← g.isAssigned then throwError "factory received a partially solved goal"
    discard <| base g cfg
    discard <| rank "Will this premise set finish the goal?" g #[.str "first", .str "second"]
    pure #[{ name := ``And.intro, score := 1 }]
  let tactics : TacticSet := {
    finish := fun ctx => pure <| if ctx.premises.contains ``And.intro then
      #["exact ⟨True.intro, True.intro⟩"] else #["constructor"] }
  let stats ← IO.mkRef ({} : Stats)
  solve [goal.mvarId!] base (fun _ cs => pure { order := (List.range cs.size).toArray }) stats
    { maxMillis := 30000, maxCalls := 1, deferPremiseGuidance := true } tactics (some factory)
  let s ← stats.get
  unless (← queries.get) == 2 && (← goal.mvarId!.isAssigned) &&
      s.unguidedPremiseAttempts == 1 && s.unguidedPremiseFinishes == 0 &&
      s.selectorRankCalls == 1 && s.premiseRankCalls == 1 && s.rankCalls == 1 do
    throwError "failed early finishing did not restore state and reach budgeted guidance"

example : True := by check_deferred_guidance_fallback; trivial

elab "check_deferred_guidance_budget" : tactic => withMainContext do
  let target := mkApp2 (mkConst ``Or)
    (mkApp (mkConst ``JevHammerTests.unknown) (mkNatLit 0))
    (mkApp (mkConst ``JevHammerTests.unknown) (mkNatLit 1))
  for limit in #[0, 1, 3] do
    let goal ← mkFreshExprMVar target
    let calls ← IO.mkRef (0 : Nat)
    let factory : SelectorFactory := fun rank base g cfg => do
      discard <| rank "Will this premise set help?" g #[.str "first", .str "second"]
      base g cfg
    let ranker : Ranker := fun _ cs => do
      calls.modify (· + 1)
      pure { order := (List.range cs.size).toArray.reverse }
    let stats ← IO.mkRef ({} : Stats)
    let failed ← try
      solve [goal.mvarId!] JevHammerTests.branchSelector ranker stats {
        maxMillis := 30000, maxNodes := 3, maxDepth := 1, maxCalls := limit,
        deferPremiseGuidance := true, refreshPremises := false }
        (selectorFactory := some factory)
      pure false
    catch _ => pure true
    let s ← stats.get
    unless failed && !(← goal.mvarId!.isAssigned) && s.unguidedPremiseAttempts == 1 &&
        s.unguidedPremiseFinishes == 0 && s.selectorRankCalls == min limit 1 &&
        s.rankCalls == s.premiseRankCalls + s.stateRankCalls &&
        s.rankCalls == (← calls.get) && s.rankCalls <= limit && s.rankFailures == 0 do
      throwError "deferred guidance broke shared budget accounting or failure atomicity"
    if limit == 3 && s.stateRankCalls == 0 then
      throwError "deferred premise guidance disabled later proof-state guidance"

example : True := by check_deferred_guidance_budget; trivial

elab "check_deferred_guidance_clock" : tactic => withMainContext do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let queries ← IO.mkRef (0 : Nat)
  let factories ← IO.mkRef (0 : Nat)
  let base : Selector := fun _ _ => do
    queries.modify (· + 1)
    IO.sleep 550
    pure #[]
  let factory : SelectorFactory := fun _ base g cfg => do
    factories.modify (· + 1)
    base g cfg
  let calls ← IO.mkRef (0 : Nat)
  let ranker : Ranker := fun _ cs => do
    calls.modify (· + 1)
    pure { order := (List.range cs.size).toArray }
  let stats ← IO.mkRef ({} : Stats)
  let failed ← try
    solve [goal.mvarId!] base ranker stats { maxMillis := 500, deferPremiseGuidance := true }
      {} (some factory)
    pure false
  catch _ => pure true
  unless failed && (← queries.get) == 1 && (← factories.get) == 0 && (← calls.get) == 0 &&
      (← stats.get).exhausted && !(← goal.mvarId!.isAssigned) do
    throwError "the early stage reset the clock or allowed guidance after expiry"

example : True := by check_deferred_guidance_clock; trivial

elab "check_deferred_guidance_atomic" : tactic => withMainContext do
  let first ← mkFreshExprMVar (mkConst ``True)
  let second ← mkFreshExprMVar (mkConst ``False)
  let stats ← IO.mkRef ({} : Stats)
  let failed ← try
    solve [first.mvarId!, second.mvarId!] trueSelector
      (fun _ cs => pure { order := (List.range cs.size).toArray }) stats {
        maxMillis := 30000, deferPremiseGuidance := true, guidePremises := true }
      trueTactics
    pure false
  catch _ => pure true
  unless failed && !(← first.mvarId!.isAssigned) && !(← second.mvarId!.isAssigned) &&
      (← stats.get).unguidedPremiseFinishes == 1 do
    throwError "failure on a later goal retained an early-stage proof assignment"

example : True := by check_deferred_guidance_atomic; trivial

end JevHammerTests.DeferredGuidance
