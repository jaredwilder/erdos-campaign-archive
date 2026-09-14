import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

open Filter in
def erdosF (n : Nat) : ℝ :=
  ∑ p ∈ (Finset.range n).filter Nat.Prime, 1 / (((n - p : Nat) : ℝ))

theorem msl_erdos950_lem_r003_all_c1 : Filter.liminf erdosF Filter.atTop = (1 : ℝ) := by sorry
