import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def blockPrimeFactors (n : Nat) (k : Nat) : Finset Nat :=
  (Finset.prod (Finset.Icc (1 : Nat) k) (fun i : Nat => n + i)).primeFactors

def samePrimeBlockFactors (k₁ : Nat) (k₂ : Nat) (n₁ : Nat) (n₂ : Nat) : Prop :=
  blockPrimeFactors n₁ k₁ = blockPrimeFactors n₂ k₂

def residueCheckPass (k₁ : Nat) (k₂ : Nat) (n₁ : Nat) (n₂ : Nat) : Prop :=
  ∀ p : Nat, Nat.Prime p → (2 : Nat) ≤ p → p ≤ k₁ →
    ∃ j : Nat, j ∈ Finset.Icc (1 : Nat) k₂ ∧ p ∣ n₂ + j

def sharedPrimeAcrossGap (k₁ : Nat) (k₂ : Nat) (n₁ : Nat) (n₂ : Nat) : Prop :=
  ∃ p : Nat, Nat.Prime p ∧ (2 : Nat) ≤ p ∧ p ≤ k₁ ∧
    ∃ i : Nat, i ∈ Finset.Icc (1 : Nat) k₁ ∧
      ∃ j : Nat, j ∈ Finset.Icc (1 : Nat) k₂ ∧
        p ∣ n₁ + i ∧ p ∣ n₁ + (n₂ - n₁) + j

theorem msl_erdos931_lem_r006_l1_composition (k₁ : Nat) (k₂ : Nat) (n₁ : Nat) (n₂ : Nat) : ((∀ (k : Nat), (3 : Nat) ≤ k → ∃ p : Nat, Nat.Prime p ∧ (2 : Nat) ≤ p ∧ p ≤ k) ∧ (∀ (n : Nat) (k : Nat) (p : Nat), Nat.Prime p → p ≤ k → ∃ i : Nat, i ∈ Finset.Icc (1 : Nat) k ∧ p ∣ n + i) ∧ (∀ (j : Nat) (p : Nat), n₁ ≤ n₂ → p ∣ n₂ + j → p ∣ n₁ + (n₂ - n₁) + j) ∧ (samePrimeBlockFactors k₁ k₂ n₁ n₂ → residueCheckPass k₁ k₂ n₁ n₂)) → ((3 : Nat) ≤ k₂ → k₂ ≤ k₁ → n₁ + k₁ ≤ n₂ → residueCheckPass k₁ k₂ n₁ n₂ → sharedPrimeAcrossGap k₁ k₂ n₁ n₂) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos931_lem_r006_l1_composition
