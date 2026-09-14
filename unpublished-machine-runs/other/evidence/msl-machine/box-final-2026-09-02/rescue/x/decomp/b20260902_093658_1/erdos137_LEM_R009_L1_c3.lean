import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def oddPart (n : Nat) : Nat := n / 2 ^ (n.factorization 2)

theorem msl_erdos137_lem_r009_l1_c3 (m : Nat) : blockProduct (2 * m) 3 % 8 = 0 := by sorry
