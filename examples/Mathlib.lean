-- Compile this file in a project depending on both JevHammer and Mathlib.
-- The core JevHammer package intentionally does not build this module.
import JevHammer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open JevHammer

def mathlibTactics : TacticSet := {
  defaultTactics with
  close := defaultTactics.close.append (.fixed #["ring", "linarith", "norm_num"])
  steps := .interleave #[defaultTactics.steps, .fixed #["ring_nf at *"]] }

example (x y : Int) : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  jev_hammer with mathlibTactics

-- A completely replaced collection can use just the downstream ring tactic.
example (α : Type) [CommRing α] (x y : α) :
    (x + y)^2 = x^2 + 2*x*y + y^2 := by
  jev_hammer with { close := .fixed #["ring"] }

example (x y : Int) (h : x < y) : x + 1 ≤ y := by
  jev_hammer with { close := .fixed #["linarith"] }

example : (2 : Int)^10 = 1024 := by
  jev_hammer with { close := .fixed #["norm_num"] }
