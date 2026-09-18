import JevHammer

open Lean Meta Elab Tactic LibrarySuggestions JevHammer

set_option Elab.async false
set_option maxHeartbeats 4000000

namespace JevHammerTests

def counted : Nat → Nat
  | 0 => 0
  | n + 1 => counted n + 2

private theorem counted_eq (n : Nat) : counted n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [counted, ih]; omega

def countedSelector : Selector := fun _ config => do
  unless config.caller == some "jev_hammer" do throwError "incorrect caller"
  return #[{ name := ``counted_eq, score := 1 }].take config.maxSuggestions

def forbiddenSelector : Selector := fun _ _ => throwError "selector should not run on this goal"

elab "check_exact_suggestion" : tactic => do
  let before := (← getThe Core.State).messages.toList.length
  evalTactic (← `(tactic| jev_hammer using countedSelector))
  let messages := (← getThe Core.State).messages.toList.drop before
  let text ← messages.mapM fun message => message.data.toString
  unless text.any (·.contains "Try this:") &&
      !(text.any (·.contains "corresponding tactic failed")) do
    throwError "the exact suggestion did not successfully replay"

-- Both the registered engine and a per-call selector work. These tests use an
-- untagged private theorem, so neither global simp nor grind can discover it.
set_library_suggestions countedSelector

example (n : Nat) : counted n = 2 * n := by jev_hammer
example (n : Nat) : counted n = 2 * n := by jev_hammer using countedSelector
example (n : Nat) : counted n = 2 * n := by
  jev_hammer using fun goal config => countedSelector goal config
example (n : Nat) : counted n = 2 * n := by check_exact_suggestion

-- The cheap prefix must not access the selector, credentials, or pass.
example : True := by jev_hammer using forbiddenSelector
example : True := by jev_hammer_pass "nonexistent-test-entry" using forbiddenSelector
example (p : Prop) (h : p) : p := by jev_hammer
example (a b : Nat) (h : a < b) : a + 1 ≤ b := by jev_hammer

-- Omega certificates need not pretty-print to elaboratable exact terms. Its
-- short tactic suggestion must instead be checked in the original state.
elab "check_omega_suggestion" : tactic => do
  let before := (← getThe Core.State).messages.toList.length
  evalTactic (← `(tactic| jev_hammer using forbiddenSelector))
  let messages := (← getThe Core.State).messages.toList.drop before
  let text ← messages.mapM fun message => message.data.toString
  unless text.any (·.contains "Try this:") && text.any (·.contains "omega") &&
      !(text.any (·.contains "corresponding tactic failed")) do
    throwError "the omega suggestion did not successfully replay"

example (a b : Nat) : a + b = b + a := by check_omega_suggestion

elab "check_selector_contract" : tactic => withMainContext do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let names ← selectPremises (fun g config => do
    unless config.maxSuggestions == 2 && !(← config.filter `NoSuchDeclaration) do
      throwError "selector did not receive its limit and availability filter"
    g.assign (mkConst ``True.intro)
    addDecl <| .axiomDecl {
      name := `JevHammerTests.selectorTemporary, levelParams := [], type := mkConst ``True,
      isUnsafe := false }
    return #[
      { name := `JevHammerTests.selectorTemporary, score := 1 },
      { name := `NoSuchDeclaration, score := 1 },
      { name := ``And.comm, score := 0.1 },
      { name := ``And.comm, score := 0.9 },
      { name := ``Or.comm, score := 0.2 },
      { name := ``True.intro, score := 1 }]) goal.mvarId! 2
  unless names == #[``And.comm, ``Or.comm] do
    throwError "selector order, deduplication, or bound violated"
  if (← goal.mvarId!.isAssigned) || (← getEnv).contains `JevHammerTests.selectorTemporary then
    throwError "selector leaked metavariable assignments or declarations"
  let names ← selectPremises forbiddenSelector goal.mvarId! 0
  unless names.isEmpty do throwError "zero premise budget was ignored"

example : True := by check_selector_contract; trivial

opaque unknown : Nat → Prop := fun _ => False

def branchSelector : Selector := fun _ _ => pure #[
  { name := ``And.comm, score := 1 }, { name := ``Or.comm, score := 0.5 }]

elab "check_state_guidance" : tactic => withMainContext do
  for guide in #[false, true] do
    let target := mkApp2 (mkConst ``Or)
      (mkApp (mkConst ``unknown) (mkNatLit 0))
      (mkApp (mkConst ``unknown) (mkNatLit 1))
    let goal ← mkFreshExprMVar target
    let requests ← IO.mkRef (#[] : Array Json)
    let ranker : Ranker := fun state choices => do
      requests.modify (·.push state)
      IO.ofExcept (Scoring.request state choices "test-model").validate
      return { order := (List.range choices.size).toArray.reverse }
    let stats ← IO.mkRef ({} : Stats)
    let failed ← try
      solve [goal.mvarId!] branchSelector ranker stats {
        maxMillis := 30000, maxNodes := 3, maxDepth := 1, maxCalls := 3,
        guidePremises := guide }
      pure false
    catch _ => pure true
    let requests ← requests.get
    let s ← stats.get
    unless failed && !(← goal.mvarId!.isAssigned) do
      throwError "failed search leaked a proof assignment"
    unless requests.any (fun r => r.getObjValD "task" == .str "continuations") &&
        s.stateRankCalls > 0 && s.rankFailures == 0 do
      throwError "proof-state heuristic was not exercised"
    unless s.premiseRankCalls == (if guide then 1 else 0) do
      throwError "premise ordering did not respect guidePremises"

example : True := by check_state_guidance; trivial

elab "check_rollback_and_failures" : tactic => withMainContext do
  for failure in #[0, 1] do
    let first ← mkFreshExprMVar (mkConst ``True)
    let target := mkApp2 (mkConst ``Or)
      (mkApp (mkConst ``unknown) (mkNatLit 0))
      (mkApp (mkConst ``unknown) (mkNatLit 1))
    let goal ← mkFreshExprMVar target
    let ranker : Ranker := fun _ _ =>
      if failure == 0 then pure { order := #[0, 0] }
      else throw (IO.userError "offline simulated API failure")
    let stats ← IO.mkRef ({} : Stats)
    let failed ← try
      solve [first.mvarId!, goal.mvarId!] branchSelector ranker stats {
        maxMillis := 30000, maxNodes := 3, maxDepth := 1, maxCalls := 1 }
      pure false
    catch _ => pure true
    unless failed && !(← first.mvarId!.isAssigned) && !(← goal.mvarId!.isAssigned) do
      throwError "multi-goal failure was not atomic"
    unless (← stats.get).rankCalls == 1 && (← stats.get).rankFailures == 1 do
      throwError "ranking failure or shared call limit was not recorded"
  let goal ← mkFreshExprMVar (mkConst ``True)
  let stats ← IO.mkRef ({} : Stats)
  let failed ← try
    solve [goal.mvarId!] forbiddenSelector (fun _ _ => pure { order := #[] }) stats
      { maxMillis := 0 }
    pure false
  catch _ => pure true
  unless failed && !(← goal.mvarId!.isAssigned) && (← stats.get).exhausted do
    throwError "zero time budget was ignored"

example : True := by check_rollback_and_failures; trivial

elab "check_no_admissions" : tactic => withMainContext do
  let saved ← saveState
  for code in #["sorry", "admit"] do
    let goal ← mkFreshExprMVar (mkConst ``False)
    let failed ← try
      discard <| runCode goal.mvarId! code 15000
      pure false
    catch _ => pure true
    saved.restore
    unless failed do throwError "speculative tactics accepted an admission"
  let unresolved ← mkFreshExprMVar (mkConst ``True)
  let failed ← try
    discard <| kernelCheckClosure unresolved
    pure false
  catch _ => pure true
  unless failed do throwError "unresolved proof passed the kernel-closure gate"

example : True := by check_no_admissions; trivial

-- A selector exception must be atomic across earlier solved goals as well.
elab "check_selector_exception" : tactic => withMainContext do
  let first ← mkFreshExprMVar (mkConst ``True)
  let last ← mkFreshExprMVar (mkConst ``False)
  let stats ← IO.mkRef ({} : Stats)
  let failed ← try
    solve [first.mvarId!, last.mvarId!] forbiddenSelector
      (fun _ _ => throw (IO.userError "unexpected ranking")) stats
    pure false
  catch _ => pure true
  unless failed && !(← first.mvarId!.isAssigned) && !(← last.mvarId!.isAssigned) do
    throwError "selector exception kept partial results"

example : True := by check_selector_exception; trivial

end JevHammerTests
