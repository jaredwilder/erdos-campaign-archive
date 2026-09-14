import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def erdos1108_A : Nat → Prop := fun s => ∃ (S : Finset Nat), s = ∑ n ∈ S, (n : Nat).factorial

def erdos1108_Powerful (a : Nat) : Prop := ∀ (p : Nat), p.Prime → p ∣ a → p * p ∣ a

theorem msl_erdos1108_demand_r001_r001_1_c2 : ({a : Nat | erdos1108_A a ∧ erdos1108_Powerful a}).Finite := by sorry
