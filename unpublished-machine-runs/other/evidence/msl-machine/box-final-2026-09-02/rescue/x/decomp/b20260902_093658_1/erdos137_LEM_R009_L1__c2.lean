import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos137_lem_r009_l1_c2 (n : Nat) : n ∈ Finset.Icc (1 : Nat) (999 : Nat) → ¬ (powerful n ∧ powerful (n + 1) ∧ powerful (n + 2)) := by sorry
