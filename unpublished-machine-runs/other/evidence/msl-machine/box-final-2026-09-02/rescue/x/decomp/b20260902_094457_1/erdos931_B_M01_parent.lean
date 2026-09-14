import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def goodPair (k₁ k₂ n₁ n₂ : Nat) : Prop :=
  n₁ + k₁ ≤ n₂ ∧
    (∏ i ∈ Finset.Icc (1 : Nat) k₁, n₁ + i).primeFactors =
      (∏ j ∈ Finset.Icc (1 : Nat) k₂, n₂ + j).primeFactors

def goodSet (k₁ k₂ : Nat) : Set (Nat × Nat) :=
  {p : Nat × Nat | goodPair k₁ k₂ p.1 p.2}

theorem msl_erdos931_b_m01_parent : ∃ (k₁ k₂ : Nat), (3 : Nat) ≤ k₂ ∧ k₂ ≤ k₁ ∧ (goodSet k₁ k₂).Infinite := by sorry
