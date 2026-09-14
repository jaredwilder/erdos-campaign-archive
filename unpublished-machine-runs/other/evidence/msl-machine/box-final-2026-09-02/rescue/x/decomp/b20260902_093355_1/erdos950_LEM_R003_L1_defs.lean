import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def erdos950f (n : Nat) : ℝ :=
  ∑ p ∈ Nat.primesBelow n, (1 : ℝ) / ((n : ℝ) - (p : ℝ))
