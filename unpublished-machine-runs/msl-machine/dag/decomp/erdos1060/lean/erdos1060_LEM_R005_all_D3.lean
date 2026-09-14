import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def sigma (k : Nat) : Nat := ∑ d ∈ Nat.divisors k, d

def fCount (n : Nat) : Nat :=
  (Finset.filter (fun (k : Nat) => k * sigma k = n) (Finset.Icc 1 n)).card

theorem msl_erdos1060_lem_r005_all_c3 (n : Nat) : fCount n ≤ n := by sorry
