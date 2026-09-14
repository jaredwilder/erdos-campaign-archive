import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos137_lem_r009_l1_c3 (n : Nat) : n ∈ Finset.Icc (1 : Nat) (6 : Nat) → ¬ powerful (blockProduct n (4 : Nat)) := by sorry
