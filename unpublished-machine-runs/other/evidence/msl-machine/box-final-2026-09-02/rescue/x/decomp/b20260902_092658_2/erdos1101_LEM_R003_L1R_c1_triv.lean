import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos1101_lem_r003_l1r_c1_triv : (1807 : ℕ) = 13 * 139 := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
