import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def CrossLengthFree (A : Set Nat) : Prop :=
  ∀ (r s : Nat) (a : Fin r → Nat) (b : Fin s → Nat),
    (∀ (i : Fin r), a i ∈ A) → (∀ (j : Fin s), b j ∈ A) →
      ((∏ i : Fin r, a i) = (∏ j : Fin s, b j)) → r = s

def DensAbove (A : Set Nat) (c : ℝ) : Prop :=
  ∀ (N : Nat), ∃ (M : Nat), ∀ (n : Nat), n ≥ M →
    (((Finset.Icc 1 n).filter (fun x => x ∈ A)).card : ℝ) > c * (n : ℝ)
