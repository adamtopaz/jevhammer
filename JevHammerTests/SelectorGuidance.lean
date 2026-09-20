import JevHammerTests.Regression

open Lean Meta Elab Tactic LibrarySuggestions JevHammer JevPilot

set_option Elab.async false
set_option maxHeartbeats 4000000

namespace JevHammerTests.SelectorGuidance

def passthrough : SelectorFactory := fun _ base => base

def forbidden : SelectorFactory := fun _ _ => fun _ _ =>
  throwError "cheap closing must not query a guided selector"

-- Keep the selected private lemma in this module: imported private names are
-- deliberately unavailable to the tactic parser's premise-name rendering.
private theorem guidedCounted_eq (n : Nat) : JevHammerTests.counted n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [JevHammerTests.counted, ih]; omega

def guidedSelector : Selector := fun _ cfg =>
  pure (#[{ name := ``guidedCounted_eq, score := 1 }].take cfg.maxSuggestions)

example : True := by jev_hammer guiding forbidden
example : True := by jev_hammer_pass "nonexistent-test-entry" guiding forbidden
example (n : Nat) : JevHammerTests.counted n = 2 * n := by
  jev_hammer using guidedSelector guiding passthrough
example : True := by
  jev_hammer with { close := .fixed #["trivial"] }
    using (fun _ _ => pure #[]) guiding (fun _ base => base)

private def question : String := "Would this direction find useful premises for this goal?"
private def choices : Array Json := #[.str "do not expand", .str "expand forward"]
private def target : Expr := mkApp2 (mkConst ``Or)
  (mkApp (mkConst ``JevHammerTests.unknown) (mkNatLit 0))
  (mkApp (mkConst ``JevHammerTests.unknown) (mkNatLit 1))

elab "check_selector_guidance_budget" : tactic => withMainContext do
  for limit in #[0, 1, 3] do
    let goal ← mkFreshExprMVar target
    let calls ← IO.mkRef (#[] : Array Json)
    let observed ← IO.mkRef (#[] : Array (Array Nat))
    let baseSeen ← IO.mkRef false
    let base : Selector := fun g cfg => do
      baseSeen.set true
      JevHammerTests.branchSelector g cfg
    let factory : SelectorFactory := fun rank base g cfg => do
      unless (← rank question g #[]) == #[] &&
          (← rank question g #[.str "only choice"]) == #[0] do
        throwError "zero/single choice fallback changed"
      let first ← rank question g choices
      observed.modify (·.push first)
      let second ← rank question g choices
      observed.modify (·.push second)
      base g cfg
    let ranker : Ranker := fun state cs => do
      calls.modify (·.push state)
      IO.ofExcept (Scoring.request state cs "offline-test").validate
      if state.getObjValD "task" == .str "selector" then
        unless state.getObjValD "selector_question" == .str question &&
            state.getObjValD "independent_scores" == .bool true &&
            state.getObjValD "goal" != Json.null do
          throw <| IO.userError "selector callback lost its typed request contract"
      return { order := (List.range cs.size).toArray.reverse }
    let stats ← IO.mkRef ({} : Stats)
    let failed ← try
      solve [goal.mvarId!] base ranker stats {
        maxMillis := 30000, maxNodes := 3, maxDepth := 1,
        maxCalls := limit, refreshPremises := false }
        (selectorFactory := some factory)
      pure false
    catch _ => pure true
    let s ← stats.get
    let orders ← observed.get
    let expectedFirst := if limit == 0 then #[0, 1] else #[1, 0]
    let expectedSecond := if limit < 2 then #[0, 1] else #[1, 0]
    unless failed && !(← goal.mvarId!.isAssigned) && (← baseSeen.get) &&
        orders == #[expectedFirst, expectedSecond] do
      throwError "guided selector lost base selection, fallback order, or atomicity"
    unless s.selectorRankCalls == min limit 2 && s.premiseRankCalls == s.selectorRankCalls &&
        s.rankCalls == s.premiseRankCalls + s.stateRankCalls && s.rankCalls <= limit &&
        s.rankCalls == (← calls.get).size && s.rankFailures == 0 do
      throwError "selector and proof states did not share the same call accounting"
    if limit == 3 && s.stateRankCalls == 0 then
      throwError "selector guidance disabled subsequent proof-state guidance"

example : True := by check_selector_guidance_budget; trivial

elab "check_selector_guidance_failure" : tactic => withMainContext do
  for mode in #[0, 1] do
    let goal ← mkFreshExprMVar target
    let observed ← IO.mkRef (#[] : Array Nat)
    let factory : SelectorFactory := fun rank base g cfg => do
      observed.set (← rank question g choices)
      base g cfg
    let ranker : Ranker := fun _ _ =>
      if mode == 0 then pure { order := #[0, 0] }
      else throw <| IO.userError "offline transport failure"
    let stats ← IO.mkRef ({} : Stats)
    let failed ← try
      solve [goal.mvarId!] LibrarySuggestions.empty ranker stats {
        maxMillis := 30000, maxCalls := 1, maxNodes := 1, refreshPremises := false }
        (tactics := {}) (selectorFactory := some factory)
      pure false
    catch _ => pure true
    let s ← stats.get
    unless failed && !(← goal.mvarId!.isAssigned) && (← observed.get) == #[0, 1] &&
        s.selectorRankCalls == 1 && s.premiseRankCalls == 1 &&
        s.rankCalls == 1 && s.rankFailures == 1 do
      throwError "selector failure did not use shared fallback and accounting"

example : True := by check_selector_guidance_failure; trivial

elab "check_selector_question_required" : tactic => withMainContext do
  let goal ← mkFreshExprMVar target
  let rejected ← IO.mkRef false
  let calls ← IO.mkRef (0 : Nat)
  let factory : SelectorFactory := fun rank base g cfg => do
    try
      discard <| rank "" g choices
    catch e =>
      rejected.set ((← e.toMessageData.toString).contains "mathematical question")
    base g cfg
  let ranker : Ranker := fun _ _ => do
    calls.modify (· + 1)
    pure { order := #[1, 0] }
  let stats ← IO.mkRef ({} : Stats)
  try
    solve [goal.mvarId!] LibrarySuggestions.empty ranker stats {}
      (tactics := {}) (selectorFactory := some factory)
  catch _ => pure ()
  unless (← rejected.get) && (← calls.get) == 0 do
    throwError "empty selector question reached the ranker"

example : True := by check_selector_question_required; trivial

elab "check_selector_guidance_time" : tactic => withMainContext do
  let goal ← mkFreshExprMVar target
  let entered ← IO.mkRef false
  let calls ← IO.mkRef (0 : Nat)
  let factory : SelectorFactory := fun rank base g cfg => do
    entered.set true
    IO.sleep 550
    discard <| rank question g choices
    base g cfg
  let ranker : Ranker := fun _ _ => do
    calls.modify (· + 1)
    pure { order := #[1, 0] }
  let stats ← IO.mkRef ({} : Stats)
  let failed ← try
    solve [goal.mvarId!] LibrarySuggestions.empty ranker stats { maxMillis := 500 }
      (tactics := {}) (selectorFactory := some factory)
    pure false
  catch _ => pure true
  unless failed && (← entered.get) && (← calls.get) == 0 &&
      (← stats.get).exhausted && !(← goal.mvarId!.isAssigned) do
    throwError "guided selection reset the search clock or sent a late request"

example : True := by check_selector_guidance_time; trivial

run_cmd do
  -- Selector candidates are opaque mathematical actions: a field called
  -- 'remaining' must not trigger proof-continuation compaction.
  let action := Json.mkObj [("direction", .str "backward"),
    ("remaining", .arr #[Json.mkObj [("target", .str "x"), ("context", .arr #[])]])]
  let state := Json.mkObj [("task", .str "selector"),
    ("selector_question", .str question), ("independent_scores", .bool true),
    ("goal", Json.mkObj [("target", .str "G"), ("context", .arr #[])])]
  let request := Scoring.request state #[action, .str "none"] "offline-test"
  IO.ofExcept request.validate
  unless request.questions.size == 2 do throwError "selector choices were combined"
  let some (_, TypeSafe.Question.noul body _) := request.questions[0]?
    | throwError "selector question did not use independent scores"
  unless body.getObjValD "question" == .str question &&
      body.getObjValD "candidate" == action do
    throwError "selector mathematical question or candidate was replaced"

end JevHammerTests.SelectorGuidance
