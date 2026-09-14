import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos1101_lem_r003_l1r_c2_triv : Nat.Coprime (1807 : ℕ) (1806 : ℕ) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
