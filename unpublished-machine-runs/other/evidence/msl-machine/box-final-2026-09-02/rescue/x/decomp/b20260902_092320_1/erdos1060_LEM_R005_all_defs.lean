import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def sigma (k : Nat) : Nat := ∑ d ∈ Nat.divisors k, d

def fCount (n : Nat) : Nat :=
  (Finset.filter (fun (k : Nat) => k * sigma k = n) (Finset.Icc 1 n)).card
