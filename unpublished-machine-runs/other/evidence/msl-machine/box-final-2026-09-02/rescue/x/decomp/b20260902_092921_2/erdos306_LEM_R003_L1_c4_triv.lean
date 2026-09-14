import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def erdos306R003L : Finset ℕ := {6, 10, 14, 15, 21, 22}

theorem msl_erdos306_lem_r003_l1_c4_triv : (2310:ℚ) * ((1:ℚ)/6 + 1/10 + 1/14 + 1/15 + 1/21 + 1/22) = 1150 := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
