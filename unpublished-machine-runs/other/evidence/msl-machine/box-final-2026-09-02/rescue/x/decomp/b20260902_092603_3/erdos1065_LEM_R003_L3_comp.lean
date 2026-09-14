import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def IsTwoPowQ (p k q : Nat) : Prop := p.Prime ∧ q.Prime ∧ p = 2 ^ k * q + 1

def CompleteRows (S : Finset Nat) : Prop :=
  ∀ (k : Nat), (∃ (p q : Nat), p ≤ 200 ∧ q ≤ 100 ∧ IsTwoPowQ p k q) → k ∈ S

theorem msl_erdos1065_lem_r003_l3_composition (S : Finset Nat) : ((∃ (p : Nat), p ∈ Icc 2 100 → False ∨ ∃ (q : Nat), q ∈ Icc 2 100 ∧ p ≤ 200 ∧ q ≤ 100 ∧ IsTwoPowQ p 0 q ∧ p = q + 1) ∧ (∃ (p : Nat), p ∈ Icc 2 100 → False ∨ ∃ (q : Nat), q ∈ Icc 2 100 ∧ p ≤ 200 ∧ q ≤ 100 ∧ IsTwoPowQ p 3 q ∧ p = 2 ^ (3 : Nat) * q + 1) ∧ (∃ (p : Nat), p ∈ Icc 2 200 → False ∨ ∃ (q : Nat), q ∈ Icc 2 100 ∧ p ≤ 200 ∧ q ≤ 100 ∧ IsTwoPowQ p 6 q ∧ p = 2 ^ (6 : Nat) * q + 1)) → ((S.card = 16) → CompleteRows S → ({0, 3, 6} : Finset Nat) ⊆ S) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos1065_lem_r003_l3_composition
