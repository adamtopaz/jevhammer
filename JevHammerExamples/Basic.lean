import JevHammer
import Lean.LibrarySuggestions.Default

-- This import registers Lean's built-in Sine Qua Non / current-file selector.
-- A downstream package can instead register any other standard Selector.

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  jev_hammer

example (n : Nat) : n + 0 = n := by
  jev_hammer

example (p : Prop) (h : p) : p := by
  jev_hammer using Lean.LibrarySuggestions.empty

-- If search reaches a nontrivial proof-state decision, jev_hammer reads
-- TYPESAFE_API_KEY and calls Jev. These examples close in the cheap prefix.
-- To use pass instead, write: jev_hammer_pass "your/password-store/entry".
