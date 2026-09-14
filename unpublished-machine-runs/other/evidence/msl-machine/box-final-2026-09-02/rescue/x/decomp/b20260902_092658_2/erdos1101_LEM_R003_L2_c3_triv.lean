import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def sylv : Nat → Nat
  | 0 => 2
  | n+1 => sylv n * (sylv n - 1) + 1

theorem msl_erdos1101_lem_r003_l2_c3_triv (c : ℝ) : 0 < c → ∃ (n : ℕ), (sylv n : ℝ) > Real.exp (c * (n : ℝ)) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
