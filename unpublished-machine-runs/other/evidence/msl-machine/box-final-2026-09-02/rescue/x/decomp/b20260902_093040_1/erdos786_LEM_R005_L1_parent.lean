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

theorem msl_erdos786_lem_r005_l1_parent (ε : ℝ) (hε : ε > 0) : ∀ (ε : ℝ), ε > 0 → ∃ (A : Set Nat),
 (1 ∉ A) ∧
 (DensAbove A (1 - ε)) ∧
 (CrossLengthFree A) ∧
 (∀ (δ : ℝ), δ > 0 → ∃ (N : Nat) (B : Finset Nat),
  (B ⊆ Finset.Icc 1 N) ∧
  (((B.card : ℝ) > (1 - δ) * (N : ℝ))) ∧
  (∀ (r s : Nat) (a : Fin r → Nat) (b : Fin s → Nat),
   (∀ (i : Fin r), a i ∈ (B : Set Nat)) → (∀ (j : Fin s), b j ∈ (B : Set Nat)) →
    ((∏ i : Fin r, a i) = (∏ j : Fin s, b j)) → r = s)) := by sorry
