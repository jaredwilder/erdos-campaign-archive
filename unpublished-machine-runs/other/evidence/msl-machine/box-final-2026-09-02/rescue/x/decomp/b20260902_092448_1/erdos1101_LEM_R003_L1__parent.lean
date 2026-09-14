import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Finset

def uu : Nat → Nat
  | 0 => 0
  | 1 => 2
  | (n+2) => (∏ i in Icc 1 (n+1), uu i) + 1
termination_by v => v

def P : Nat → Nat := fun (n : Nat) => ∏ i in Icc 1 n, uu i

theorem msl_erdos1101_lem_r003_l1_parent : (∀ n : Nat, n ∈ Icc 1 7 → uu n < uu (n+1)) ∧ (∀ i j : Nat, 1 ≤ i → i < j → (uu j) % (uu i) = 1) ∧ (∀ n : Nat, 1 ≤ n → P n ≥ 2 ^ (2 ^ (n - 1))) ∧ (∀ n : Nat, n ∈ Icc 2 8 → ∀ i : Nat, i ∈ Icc 1 8 → ¬ ((uu i) ∣ (P n - 1))) ∧ (∀ x : Nat, x ∈ Icc 2 (P 8 * uu 9) → ∃ t : Nat, t ∈ Icc 1 8 ∧ P t ≤ x ∧ x < P t * uu (t+1)) := by sorry
