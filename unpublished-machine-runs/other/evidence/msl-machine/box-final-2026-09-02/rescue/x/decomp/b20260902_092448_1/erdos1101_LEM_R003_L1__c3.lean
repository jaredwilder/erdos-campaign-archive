import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Finset

def uu : Nat → Nat
  | 0 => 0
  | 1 => 2
  | (n+2) => (∏ i in Icc 1 (n+1), uu i) + 1
termination_by v => v

def P : Nat → Nat := fun (n : Nat) => ∏ i in Icc 1 n, uu i

theorem msl_erdos1101_lem_r003_l1_c3 : ∑ i ∈ Icc 1 8, (1 : ℚ) / (uu i : ℚ) < 1 := by sorry
