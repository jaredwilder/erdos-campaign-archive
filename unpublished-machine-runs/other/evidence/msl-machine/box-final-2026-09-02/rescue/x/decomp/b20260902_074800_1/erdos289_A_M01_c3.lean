import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

def runOK (a b : Nat) : Prop := a < b

def pairDistinct (k : Nat) (I : Fin k → Nat × Nat) : Prop :=
  ∀ (i j : Fin k), i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1

def pairSum (k : Nat) (I : Fin k → Nat × Nat) : Rat :=
  ∑ i : Fin k, ∑ n ∈ Icc (I i).1 (I i).2, ((n : Rat)⁻¹)

def TailScheme (k : Nat) (I : Fin k → Nat × Nat) : Prop :=
  (∀ i : Fin k, (I i).1 < (I i).2 ∧ 5 ≤ (I i).1) ∧ pairDistinct k I ∧ pairSum k I = (1 : Rat) / 6

def FullScheme (k : Nat) (I : Fin k → Nat × Nat) : Prop :=
  (∀ i : Fin k, (I i).1 < (I i).2 ∧ 2 ≤ (I i).1) ∧ pairDistinct k I ∧ pairSum k I = 1

def headI : Nat × Nat := (2, 3)

def headFam : Fin 1 → Nat × Nat := fun (_ : Fin 1) => headI

theorem msl_erdos289_a_m01_c3 : pairSum 1 headFam = (5 : Rat) / 6 ∧ (5 : Rat) / 6 + (1 : Rat) / 6 = (1 : Rat) := by sorry
