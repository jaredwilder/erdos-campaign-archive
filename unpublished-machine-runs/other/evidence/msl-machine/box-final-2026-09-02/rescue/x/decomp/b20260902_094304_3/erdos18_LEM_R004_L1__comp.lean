import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def ExactTuple (n : Nat) (S : Finset Nat) (c : Nat) : Prop :=
  (∀ d ∈ S, 1 ≤ d ∧ d ∣ n) ∧ S.sum id = n - 1 ∧ S.card = c ∧
    ∀ d ∈ S, (S.erase d).sum id < n - 1

theorem msl_erdos18_lem_r004_l1_composition : ((ExactTuple (Nat.factorial 4) ({3, 4, 6, 8} : Finset Nat) 4)) → (ExactTuple (Nat.factorial 2) ({1} : Finset Nat) 1 ∧ ExactTuple (Nat.factorial 3) ({2, 3} : Finset Nat) 2 ∧ ExactTuple (Nat.factorial 4) ({3, 4, 6, 8} : Finset Nat) 4 ∧ ExactTuple (Nat.factorial 5) ({1, 8, 20, 30, 60} : Finset Nat) 5 ∧ ExactTuple (Nat.factorial 6) ({1, 6, 40, 72, 240, 360} : Finset Nat) 6) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos18_lem_r004_l1_composition
