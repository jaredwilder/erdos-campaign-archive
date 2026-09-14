import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (m : Nat) : Prop := ∀ (p : Nat), p ∣ m → p ^ 2 ∣ m

def EventuallyNotPowerful (f : Nat → Nat) : Prop :=
  ∃ (N : Nat), ∀ (n : Nat), N ≤ n → ¬ Powerful (f n)

def InfinitelyOftenPowerful (f : Nat → Nat) : Prop :=
  ∀ (N : Nat), ∃ (n : Nat), N ≤ n ∧ Powerful (f n)

theorem msl_erdos936_a_m01_c3 : EventuallyNotPowerful (fun (n : Nat) => n ! + 1) ∨ InfinitelyOftenPowerful (fun (n : Nat) => n ! + 1) := by sorry
