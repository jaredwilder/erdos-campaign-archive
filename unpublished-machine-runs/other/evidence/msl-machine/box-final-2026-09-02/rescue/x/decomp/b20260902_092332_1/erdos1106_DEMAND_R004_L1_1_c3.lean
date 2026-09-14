import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def p : Nat → Nat := fun n => (Nat.partitions n).card

def F : Nat → Nat := fun n => (Nat.factors (∏ k ∈ Icc 1 n, p k)).eraseDups.length

theorem msl_erdos1106_demand_r004_l1_1_c3 : ∀ (n : Nat), n ∈ Icc 41 60 → F n > n := by sorry
