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

-- A consuming project can extend the collection without modifying JevHammer.
macro "consumer_close" : tactic => `(tactic| exact True.intro)

def consumerTactics : JevHammer.TacticSet := {
  JevHammer.defaultTactics with
  close := (JevHammer.TacticGenerator.fixed #["consumer_close"]).append
    JevHammer.defaultTactics.close }

example : True := by jev_hammer with consumerTactics using downstreamSelector

def downstreamCustomFinish (selector : LibrarySuggestions.Selector)
    (client : JevPilot.TypeSafe.Client) (tactics : JevHammer.TacticSet) : TacticM Unit := do
  let stats ← IO.mkRef ({} : JevHammer.Stats)
  JevHammer.solve (← getGoals) selector (JevHammer.Scoring.jevRanker client) stats
    (tactics := tactics)
  setGoals []

-- Deferred guidance is available through the same public import and tactic
-- syntax. This succeeds without constructing a client or calling the factory.
def consumerPremiseTactics : JevHammer.TacticSet := {
  finish := fun ctx => pure <| if ctx.premises.contains ``Nat.add_comm then
    #["exact Nat.add_comm _ _"] else #[] }

def consumerForbiddenGuidance : JevHammer.SelectorFactory := fun _ _ _ _ =>
  throwError "the base premises should have finished before guidance"

example (a b : Nat) : a + b = b + a := by
  jev_hammer (deferPremiseGuidance := true) with consumerPremiseTactics
    using downstreamSelector guiding consumerForbiddenGuidance
