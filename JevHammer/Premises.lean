module

public meta import JevHammer.Types

public meta section
namespace JevHammer
open Lean Meta

/-- Run a standard Lean selector as a read-only query. Preserve its order, remove
duplicates and declarations absent from the original environment, and enforce
the limit even if the selector ignores it. Selector IO cannot be rolled back. -/
def selectPremises (selector : LibrarySuggestions.Selector) (goal : MVarId)
    (limit : Nat) : MetaM (Array Name) := goal.withContext do
  if limit == 0 then return #[]
  let original ← getEnv
  let saved ← saveState
  let suggestions ← try
    selector goal {
      maxSuggestions := limit, caller := "jev_hammer"
      filter := fun name => pure (original.contains name) }
    finally saved.restore
  let mut names := #[]
  for suggestion in suggestions do
    if names.size >= limit then break
    if original.contains suggestion.name && !names.contains suggestion.name then
      names := names.push suggestion.name
  return names

end JevHammer
