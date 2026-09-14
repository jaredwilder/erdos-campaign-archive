import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def sidonPrefix : List Nat := [1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97]

def cnt (N : Nat) : Nat := (sidonPrefix.filter (fun (a : Nat) => a ≤ N)).length

theorem msl_erdos340_lem_r002_l2_c3 : ((cnt 1000 : Nat) : Rat) < (1000 : Rat) ^ (1/2) := by sorry
