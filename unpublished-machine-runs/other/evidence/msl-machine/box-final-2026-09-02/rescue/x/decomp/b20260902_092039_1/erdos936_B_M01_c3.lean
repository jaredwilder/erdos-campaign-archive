import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (m : Nat) : Prop := ∀ p : Nat, p ∣ m → p ^ 2 ∣ m

theorem msl_erdos936_b_m01_c3 : ∀ (B : Nat), ((({n : Nat | n > B ∧ Powerful ((2 : Nat) ^ n + 1)}).Finite ∧ ({n : Nat | n > B ∧ Powerful ((n : Nat)! + 1)}).Finite) ↔ (({n : Nat | Powerful ((2 : Nat) ^ n + 1)}).Finite ∧ ({n : Nat | Powerful ((n : Nat)! + 1)}).Finite)) := by sorry
