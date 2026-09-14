import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def ExactTuple (n : Nat) (S : Finset Nat) (c : Nat) : Prop :=
  (∀ d ∈ S, 1 ≤ d ∧ d ∣ n) ∧ S.sum id = n - 1 ∧ S.card = c ∧
    ∀ d ∈ S, (S.erase d).sum id < n - 1

theorem msl_erdos18_lem_r004_l1_c2 : ExactTuple (Nat.factorial 3) ({2, 3} : Finset Nat) 2 := by sorry
