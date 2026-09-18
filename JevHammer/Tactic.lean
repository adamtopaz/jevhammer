module

public meta import JevHammer.Search
public meta import JevHammer.Scoring
public meta import Lean.Elab.ConfigEval
public meta import Lean.Elab.Eval
public meta import Lean.Meta.Tactic.TryThis

public meta section
namespace JevHammer
open Lean Meta Elab Tactic
open JevPilot

declare_config_elab elabHammerConfig Config

/-- Read credentials only on the first nontrivial Jev decision, and reuse the
client for subsequent decisions. Merely importing this module performs no IO. -/
def lazyJevRanker (config : Config) (passEntry : Option String := none) : IO Ranker := do
  let client ← IO.mkRef (none : Option TypeSafe.Client)
  return fun state choices => do
    let api ← match ← client.get with
      | some api => pure api
      | none => do
        let settings : TypeSafe.Config := {
          maxRetries := 0, timeoutSeconds := config.timeoutSeconds }
        let api ← (match passEntry with
          | none => TypeSafe.Client.fromEnv settings
          | some entry => TypeSafe.Client.fromPass entry settings).toIO (IO.userError ∘ toString)
        client.set (some api)
        pure api
    Scoring.jevRanker api config.model state choices

/-- Prefer a short, replayed closing tactic to an enormous rendered certificate
for direct successes, including downstream closing tactics. -/
private def suggestClosingTactic (initial : Tactic.SavedState) (code : String)
    (heartbeats : Nat) : TacticM Bool := do
  let finalState ← saveState
  let ref ← getRef
  let syntax? ← try
    initial.restore
    withMainContext do
      let goal ← getMainGoal
      let remaining ← runCode goal code heartbeats
      unless remaining.isEmpty do throwError "replacement did not close the goal"
      discard <| kernelCheckClosure (.mvar goal)
      let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `tactic code
      pure (some stx)
  catch _ => pure none
  finally finalState.restore
  if let some stx := syntax? then
    TryThis.addSuggestion ref { suggestion := (⟨stx⟩ : TSyntax `tactic) }
    return true
  return false

private def evalHammer (config : Config) (selector : LibrarySuggestions.Selector)
    (tactics : TacticSet)
    (passEntry : Option String := none) : TacticM Unit := do
  let initial ← saveState
  let original ← getEnv
  let goals ← getGoals
  let stats ← IO.mkRef ({} : Stats)
  solve goals selector (← lazyJevRanker config passEntry) stats config tactics
  setGoals []
  trace[JevHammer] "{toJson (← stats.get)}"
  if let [goal] := goals then
    let s ← stats.get
    if s.nodes == 0 && !s.winner.isEmpty then
      if ← suggestClosingTactic initial s.winner config.tacticHeartbeats then return
    let proof ← inlineAuxiliaries original (← instantiateMVars (.mvar goal))
    TryThis.addExactSuggestion (← getRef) proof (checkState? := initial) (tacticErrorAsInfo := true)

/-- A selector expression is user-supplied Lean code, never model output. -/
private def evalSelector (selector : TSyntax `term) : TacticM LibrarySuggestions.Selector := do
  unsafe Term.evalTerm LibrarySuggestions.Selector (mkConst ``LibrarySuggestions.Selector) selector

/-- Tactic collections are user-supplied Lean code, independent of the selector. -/
private def evalTacticSet (tactics : TSyntax `term) : TacticM TacticSet := do
  unsafe Term.evalTerm TacticSet (mkConst ``TacticSet) tactics

/-- Use Lean's registered premise selector and Jev proof-state guidance.
`with` replaces the entire tactic collection for this invocation; `using`
supplies its premise selector. Both accept closed Lean expressions. -/
syntax (name := jevHammer) "jev_hammer" optConfig (" with " term)? (" using " term)? : tactic
/-- Read the Jev API key from the explicitly named password-store entry. -/
syntax (name := jevHammerPass) "jev_hammer_pass" str optConfig
  (" with " term)? (" using " term)? : tactic

elab_rules : tactic
  | `(tactic| jev_hammer $cfg:optConfig $[with $tactics]? $[using $selector]?) => do
    let select : LibrarySuggestions.Selector ← match selector with
      | none => pure (fun goal config => LibrarySuggestions.select goal config)
      | some stx => evalSelector stx
    let collection ← match tactics with
      | none => pure defaultTactics
      | some stx => evalTacticSet stx
    evalHammer (← elabHammerConfig cfg) select collection
  | `(tactic| jev_hammer_pass $entry:str $cfg:optConfig $[with $tactics]? $[using $selector]?) => do
    let select : LibrarySuggestions.Selector ← match selector with
      | none => pure (fun goal config => LibrarySuggestions.select goal config)
      | some stx => evalSelector stx
    let collection ← match tactics with
      | none => pure defaultTactics
      | some stx => evalTacticSet stx
    evalHammer (← elabHammerConfig cfg) select collection (some entry.getString)

end JevHammer
