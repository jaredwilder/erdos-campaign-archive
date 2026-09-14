import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos1101_lem_r003_l1r_c3_triv : ((1805 : ℚ) / (1806 : ℚ)) = (1 : ℚ)/2 + (1 : ℚ)/3 + (1 : ℚ)/7 + (1 : ℚ)/43 := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
