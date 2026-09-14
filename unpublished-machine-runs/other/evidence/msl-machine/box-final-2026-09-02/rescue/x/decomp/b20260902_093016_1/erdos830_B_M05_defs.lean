import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Classical

@[reducible] def isAmicable (a b : Nat) : Prop :=
  Nat.sigma a = Nat.sigma b ∧ Nat.sigma a = a + b

noncomputable def A (x : Nat) : Nat :=
  (Finset.filter (fun p : Nat × Nat =>
      p.1 ≤ p.2 ∧ p.1 ≤ x ∧ isAmicable p.1 p.2)
    (Finset.product (Finset.Icc 1 x) (Finset.Icc 1 x))).card
