import JevHammer

open Lean Meta Elab Tactic JevHammer

set_option Elab.async false
set_option maxHeartbeats 4000000

namespace JevHammerTacticTests

def noPremises : LibrarySuggestions.Selector := fun _ _ => pure #[]
def forbiddenRanker : Ranker := fun _ _ => throw (IO.userError "unexpected model call")

-- A replacement is complete: even True cannot close with the empty set.
example : True := by
  fail_if_success jev_hammer with {} using noPremises
  trivial

def assumptionOnly : TacticSet := { close := .fixed #["assumption"] }

example (p : Prop) (h : p) : p := by
  jev_hammer with assumptionOnly using noPremises

example (p : Prop) (h : p) : p := by
  jev_hammer_pass "nonexistent-test-entry" with assumptionOnly using noPremises

-- No implicit introductions, even before premise-assisted finishing.
example : ∀ p : Prop, p → p := by
  fail_if_success jev_hammer with { finish := .fixed #["assumption"] } using noPremises
  jev_hammer with {
    prepare := .fixed #["intros"]
    finish := .fixed #["assumption"] } using noPremises

-- Preparation can split into multiple goals. Failed preparation is skipped;
-- later preparation is applied to all resulting goals.
example : (True → True) ∧ (True → True) := by
  jev_hammer with {
    prepare := .fixed #["fail", "constructor", "intro h"]
    finish := .fixed #["exact h"] } using noPremises

-- Cleanup must be explicitly enabled; otherwise one constructor step leaves
-- both goals pending, even though they are trivial.
example : True ∧ True := by
  fail_if_success jev_hammer (maxDepth := 1) with {
    steps := .fixed #["constructor"] } using noPremises
  jev_hammer (maxDepth := 1) with {
    steps := .fixed #["constructor"]
    cleanup := .fixed #["exact True.intro"] } using noPremises

def commSelector : LibrarySuggestions.Selector := fun _ _ =>
  pure #[{ name := ``Nat.add_comm, score := 1 }]

-- The generator receives the current selected premises, config and local context.
def selectedExact : TacticGenerator := fun ctx => do
  unless ctx.config.premiseCount == 3 && ctx.premises == #[``Nat.add_comm] do
    throwError "generator received the wrong configuration or premises"
  unless (← getLCtx).getFVars.size >= 2 do throwError "missing local context"
  let name ← unresolveNameGlobal ctx.premises[0]!
  return #[s!"exact {name} _ _"]

example (a b : Nat) : a + b = b + a := by
  -- Retrieved lemmas must not enable an unconfigured premise finisher.
  fail_if_success jev_hammer with {} using commSelector
  jev_hammer (premiseCount := 3) with { finish := selectedExact } using commSelector

-- An extension may use tactics defined in a downstream file. Unknown syntax,
-- failed scripts and admissions must not stop later valid closing alternatives.
macro "downstream_close" : tactic => `(tactic| exact True.intro)

def extended : TacticSet := {
  close := (TacticGenerator.fixed #["not_an_imported_tactic", "fail", "sorry", "admit"]).append
    (.fixed #["downstream_close"]) }

elab "check_custom_suggestion" : tactic => do
  let before := (← getThe Core.State).messages.toList.length
  evalTactic (← `(tactic| jev_hammer with extended using noPremises))
  let messages := (← getThe Core.State).messages.toList.drop before
  let text ← messages.mapM fun message => message.data.toString
  unless text.any (·.contains "Try this:") && text.any (·.contains "downstream_close") &&
      !(text.any (·.contains "corresponding tactic failed")) do
    throwError "custom closing suggestion did not replay"

example : True := by check_custom_suggestion

-- Exercise the custom steps through real beam search: both successors are open
-- until the injected ranker selects the right branch, then the custom closer runs.
elab "check_custom_guidance" : tactic => withMainContext do
  let goal ← getMainGoal
  let calls ← IO.mkRef 0
  let ranker : Ranker := fun state choices => do
    unless state.getObjValD "task" == .str "continuations" && choices.size == 2 do
      throw (IO.userError "custom branches were not presented to the state ranker")
    unless choices[1]!.getObjValD "actions" == toJson (#["right"] : Array String) do
      throw (IO.userError "custom branch order changed")
    calls.modify (· + 1)
    return { order := #[1, 0] }
  let stats ← IO.mkRef ({} : Stats)
  solve [goal] noPremises ranker stats { maxDepth := 1, beamWidth := 1 } {
    close := .fixed #["assumption"]
    steps := .interleave #[.fixed #["left"], .fixed #["right"]] }
  let proof ← instantiateMVars (.mvar goal)
  unless (← calls.get) == 1 && (← stats.get).stateRankCalls == 1 &&
      proof.getAppFn.isConstOf ``Or.inr do
    throwError "custom search did not follow Jev's selected branch"
  setGoals []

example (p q : Prop) (_hp : p) (hq : q) : p ∨ q := by check_custom_guidance

elab "check_generator_isolation" : tactic => withMainContext do
  for throws in #[false, true] do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let stats ← IO.mkRef ({} : Stats)
    let generator : TacticGenerator := fun ctx => do
      ctx.goal.assign (mkConst ``True.intro)
      addDecl <| .axiomDecl {
        name := `JevHammerTacticTests.temporary,
        levelParams := [], type := mkConst ``True, isUnsafe := false }
      if throws then throwError "simulated generator failure"
      return #["exact JevHammerTacticTests.temporary"]
    let failed ← try
      solve [goal.mvarId!] noPremises forbiddenRanker stats {} { close := generator }
      pure false
    catch _ => pure true
    unless failed && !(← goal.mvarId!.isAssigned) &&
        !(← getEnv).contains `JevHammerTacticTests.temporary do
      throwError "generator state leaked into proof search"

example : True := by check_generator_isolation; trivial

-- Roll back the entire prepared root if only one of its generated subgoals closes.
elab "check_preparation_rollback" : tactic => withMainContext do
  let goal ← mkFreshExprMVar (mkApp2 (mkConst ``And) (mkConst ``True) (mkConst ``False))
  let stats ← IO.mkRef ({} : Stats)
  let failed ← try
    solve [goal.mvarId!] noPremises forbiddenRanker stats {} {
      prepare := .fixed #["constructor"]
      finish := .fixed #["exact True.intro"] }
    pure false
  catch _ => pure true
  unless failed && !(← goal.mvarId!.isAssigned) do
    throwError "partial preparation proof survived failed search"
  -- No hidden tactic attempts, even on a trivially true goal.
  let goal ← mkFreshExprMVar (mkConst ``True)
  let stats ← IO.mkRef ({} : Stats)
  let failed ← try
    solve [goal.mvarId!] noPremises forbiddenRanker stats {} {}
    pure false
  catch _ => pure true
  unless failed && !(← goal.mvarId!.isAssigned) && (← stats.get).trials == 0 do
    throwError "empty tactic set executed a hidden tactic"

example : True := by check_preparation_rollback; trivial

end JevHammerTacticTests
