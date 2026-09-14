import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def erdos1108_A : Nat → Prop := fun s => ∃ (S : Finset Nat), s = ∑ n ∈ S, (n : Nat).factorial

def erdos1108_Powerful (a : Nat) : Prop := ∀ (p : Nat), p.Prime → p ∣ a → p * p ∣ a

theorem msl_erdos1108_demand_r001_r001_1_composition (k : Nat) (hk : 2 ≤ k) : ((({a : Nat | erdos1108_A a ∧ ∃ (m : Nat), m ^ k = a}).Finite) ∧ (({a : Nat | erdos1108_A a ∧ erdos1108_Powerful a}).Finite)) → (({a : Nat | erdos1108_A a ∧ ∃ (m : Nat), m ^ k = a}).Finite ∧ ({a : Nat | erdos1108_A a ∧ erdos1108_Powerful a}).Finite) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos1108_demand_r001_r001_1_composition
