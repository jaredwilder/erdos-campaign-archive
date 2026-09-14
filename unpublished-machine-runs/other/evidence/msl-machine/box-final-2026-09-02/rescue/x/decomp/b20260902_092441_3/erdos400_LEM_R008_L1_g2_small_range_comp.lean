import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def feasiblePair (n a b : Nat) : Prop := a.factorial * b.factorial ∣ n.factorial

def excessAtLeast1 (n a b : Nat) : Prop := a + b ≥ n + 1

def witnessPair (n : Nat) : Nat × Nat := (n, 1)

def smallRange : Finset Nat := Finset.Icc (2 : Nat) (200 : Nat)

theorem msl_erdos400_lem_r008_l1_g2_small_range_composition (n : Nat) : ((2 ≤ n → feasiblePair n (witnessPair n).1 (witnessPair n).2) ∧ (2 ≤ n → excessAtLeast1 n (witnessPair n).1 (witnessPair n).2) ∧ (n ∈ smallRange → 2 ≤ n)) → (n ∈ smallRange → ∃ (a b : Nat), feasiblePair n a b ∧ excessAtLeast1 n a b) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos400_lem_r008_l1_g2_small_range_composition
