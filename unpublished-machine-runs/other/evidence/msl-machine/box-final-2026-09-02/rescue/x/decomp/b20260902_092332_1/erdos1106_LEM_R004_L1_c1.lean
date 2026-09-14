import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def p (n : Nat) : Nat := (Nat.partitions n).card

def F (n : Nat) : Nat :=
  (Nat.factors ((Finset.Icc 1 n).fold (fun (acc : Nat) (k : Nat) => acc * p k) 1)).toFinset.card

theorem msl_erdos1106_lem_r004_l1_c1 : ∀ (n : Nat), n ∈ Finset.Icc 1 30 → F n > n := by sorry
