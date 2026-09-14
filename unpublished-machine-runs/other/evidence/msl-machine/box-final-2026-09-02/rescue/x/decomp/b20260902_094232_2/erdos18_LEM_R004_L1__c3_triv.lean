import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def ExactTuple (n : Nat) (S : Finset Nat) (c : Nat) : Prop :=
  (∀ d ∈ S, 1 ≤ d ∧ d ∣ n) ∧ S.sum id = n - 1 ∧ S.card = c ∧
    ∀ d ∈ S, (S.erase d).sum id < n - 1

theorem msl_erdos18_lem_r004_l1_c3_triv : ExactTuple (Nat.factorial 4) ({3, 4, 6, 8} : Finset Nat) 4 := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
