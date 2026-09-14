import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (m : Nat) : Prop := ∀ p : Nat, p ∣ m → p ^ 2 ∣ m
