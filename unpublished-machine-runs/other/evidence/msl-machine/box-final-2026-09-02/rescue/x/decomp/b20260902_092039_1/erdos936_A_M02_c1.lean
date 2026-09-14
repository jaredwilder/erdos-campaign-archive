import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (m : Nat) : Prop := ∀ (p : Nat), p ∣ m → p ^ 2 ∣ m

def PowerfulSet (f : Nat → Nat) : Set Nat := {n : Nat | Powerful (f n)}

def Determined (f : Nat → Nat) : Prop :=
  (PowerfulSet f).Finite ∨ ¬(PowerfulSet f).Finite

def WrapperTrue (f : Nat → Nat) : Prop := (PowerfulSet f).Finite

def twoPowAdd : Nat → Nat := fun (n : Nat) => 2 ^ n + 1

def twoPowSub : Nat → Nat := fun (n : Nat) => 2 ^ n - 1

def factAdd : Nat → Nat := fun (n : Nat) => n ! + 1

def factSub : Nat → Nat := fun (n : Nat) => n ! - 1

def MixedAnswers : Prop :=
  ¬((WrapperTrue twoPowAdd) = (WrapperTrue twoPowSub) ∧
    (WrapperTrue twoPowSub) = (WrapperTrue factAdd) ∧
    (WrapperTrue factAdd) = (WrapperTrue factSub))

theorem msl_erdos936_a_m02_c1 : Determined twoPowAdd ∧ Determined twoPowSub := by sorry
