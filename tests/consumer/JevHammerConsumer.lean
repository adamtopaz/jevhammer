import JevHammer

open Lean Meta Elab Tactic

-- This module is compiled as an independent Lake package. The only public
-- import needed for either the tactic or the programmatic API is JevHammer.
def downstreamSelector : LibrarySuggestions.Selector := fun _ config =>
  pure <| #[{ name := ``Nat.add_comm, score := 1 }].take config.maxSuggestions

example (a b : Nat) : a + b = b + a := by
  jev_hammer using downstreamSelector

def downstreamFinish (selector : LibrarySuggestions.Selector)
    (client : JevPilot.TypeSafe.Client) : TacticM Unit := do
  let stats ← IO.mkRef ({} : JevHammer.Stats)
  JevHammer.solve (← getGoals) selector (JevHammer.Scoring.jevRanker client) stats
  setGoals []
