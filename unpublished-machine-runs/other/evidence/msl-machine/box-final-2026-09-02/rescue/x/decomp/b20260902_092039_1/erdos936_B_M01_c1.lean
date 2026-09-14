import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (m : Nat) : Prop := ∀ p : Nat, p ∣ m → p ^ 2 ∣ m

theorem msl_erdos936_b_m01_c1 : Powerful ((2 : Nat) ^ 3 + 1) := by sorry
