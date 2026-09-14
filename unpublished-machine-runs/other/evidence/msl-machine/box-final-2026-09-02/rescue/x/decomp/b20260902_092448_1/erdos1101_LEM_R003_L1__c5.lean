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

theorem msl_erdos1101_lem_r003_l1_c5 : ∀ x : Nat, x ∈ Icc 2 (P 8 * uu 9) → ∃ t : Nat, t ∈ Icc 1 8 ∧ P t ≤ x ∧ x < P t * uu (t+1) := by sorry
