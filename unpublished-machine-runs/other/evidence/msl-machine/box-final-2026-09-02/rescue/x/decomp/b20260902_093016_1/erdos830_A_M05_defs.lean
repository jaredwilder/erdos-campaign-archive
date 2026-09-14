import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def AmicablePair (a b : Nat) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ Nat.sigma a = Nat.sigma b ∧ Nat.sigma b = a + b

def AmicableCount (x : Nat) : Nat :=
  #{p : Nat × Nat | p.1 ≥ 1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ x ∧ AmicablePair p.1 p.2}
