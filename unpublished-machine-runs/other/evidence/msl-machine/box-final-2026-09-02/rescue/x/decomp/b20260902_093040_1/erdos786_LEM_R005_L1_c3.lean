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

theorem msl_erdos786_lem_r005_l1_c3 (A : Set Nat) : ∀ (A : Set Nat), 1 ∉ A →
 ¬ ∃ (x : Nat) (b : Fin 2 → Nat),
  (x ∈ A) ∧ (∀ (j : Fin 2), b j ∈ A) ∧
  (x = b 0 * b 1) ∧ (b 0 = 1 ∨ b 1 = 1) := by sorry
