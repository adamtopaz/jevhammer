module

public meta import Lean.Meta.Check
public meta import Lean.Elab.Tactic
public meta import Lean.Elab.Tactic.Meta

public meta section
namespace JevHammer
open Lean Meta Elab

/-- Check a lambda-closed proof, not the raw local context (whose declaration
 types can still contain assigned metavariables during elaboration). Unassigned
 universes are generalized in a *copy* for kernel checking; caller constraints are
 not assigned. Expression metavariables and admissions are never generalized away. -/
def kernelCheckClosure (proof : Expr) : MetaM Expr := do
  let closed ← instantiateMVars <| ← mkLambdaFVars (← getLCtx).getFVars proof (usedOnly := true)
  if closed.hasExprMVar || closed.hasSorry || closed.hasFVar then
    throwError "search produced an incomplete or admitted proof closure"
  let used := (collectLevelParams {} closed).params
  let closed := ((← getMCtx).levelMVarToParam used.contains (fun _ => false)
    closed `_jevKernelU).expr
  match Kernel.check (← getEnv) {} closed with
  | .ok _ => return closed
  | .error e => throwError "kernel proof-closure check failed: {e.toMessageData (← getOptions)}"

/-- `withOptions` alone does not update Core.Context.maxHeartbeats in Lean 4.34.
Set the actual context limit too, and reset the counter for this operation. -/
def withHeartbeatBudget (limit : Nat) (action : MetaM α) : MetaM α :=
  withOptions (fun o => o.set `maxHeartbeats limit) <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := limit * 1000 }) <|
      withCurrHeartbeats action

/-- Inline proof auxiliaries created by tactics such as omega. Certificates must
be replayable in the original environment, without those generated declarations. -/
def inlineAuxiliaries (original : Environment) (proof : Expr) : MetaM Expr := do
  let expanded ← Core.transform proof fun e => do
    if let .const n us := e then
      let info ← getConstInfo n
      -- Existing private declarations are available at this source location and
      -- should stay named. Expanding their bodies can make exact suggestions
      -- enormous and prevent the pretty-printed term from elaborating again.
      if !original.contains n then
        let some value := info.value? (allowOpaque := true) | throwError "new opaque constant in proof: {n}"
        return .visit (value.instantiateLevelParams info.levelParams us)
    return .continue
  Core.betaReduce expanded

/-- Tactic syntax is constructed exclusively by this program, using environment names. -/
def runCode (g : MVarId) (code : String) (heartbeats : Nat) : MetaM (List MVarId) := do
  let _ : MonadExceptOf Exception MetaM :=
    { (inferInstance : MonadExceptOf Exception MetaM) with tryCatch := tryCatchRuntimeEx }
  -- `first` disables tactic recovery, and errToSorry disables term recovery.
  -- A failed speculative tactic must throw, never create a synthetic admission.
  let input := "first | " ++ code
  let fileName := "<jevhammer>"
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `tactic input fileName
  let messages := (← getThe Core.State).messages
  -- Tactics that emit suggestions interpret syntax offsets in the active file
  -- map. These offsets refer to our script, and can land inside UTF-8 characters
  -- (or beyond EOF) in the caller's source. Keep the synthetic context scoped.
  withTheReader Core.Context (fun c => { c with
      fileName, fileMap := FileMap.ofString input, ref := stx }) <|
    withHeartbeatBudget heartbeats do
    try
      let result ← Elab.runTactic g stx { errToSorry := false }
      let after := (← getThe Core.State).messages
      if (after.hasErrors && !messages.hasErrors) ||
          (after.toList.drop messages.toList.length).any (·.severity == .error) then
        throwError "speculative tactic logged an error"
      if (← instantiateMVars (.mvar g)).hasSorry then throwError "tactic produced an admission"
      return result.1
    finally
      modifyThe Core.State fun s => { s with messages }

/-- Cheap closing tactics. Aesop is attempted when its syntax is available in
the caller's environment; importing JevHammer does not require Aesop. -/
def portfolioCodes : Array String := #[
  "solve | assumption | rfl | trivial", "solve | simp_all", "solve | omega",
  "aesop (config := { maxRuleApplications := 120 })", "grind (gen := 8)"]
end JevHammer
