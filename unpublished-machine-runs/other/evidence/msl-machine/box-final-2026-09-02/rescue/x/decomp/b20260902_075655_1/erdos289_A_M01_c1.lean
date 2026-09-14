import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset
open Filter

def Good (k : Nat) (I : Fin k → Nat × Nat) : Prop :=
  (∀ (i : Fin k), (I i).1 < (I i).2) ∧
  (∀ (i j : Fin k), i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1)

def sumQ (k : Nat) (I : Fin k → Nat × Nat) : Rat :=
  ∑ i : Fin k, ∑ n ∈ Icc (I i).1 (I i).2, ((n : Rat))⁻¹

def prepend23 (k : Nat) (T : Fin k → Nat × Nat) : Fin (k + 1) → Nat × Nat :=
  Fin.cons (2, 3) T

theorem msl_erdos289_a_m01_c1 (k : Nat) (T : Fin k → Nat × Nat) : (∀ (i : Fin k), 5 ≤ (T i).1) → Good k T → Good (k + 1) (prepend23 k T) := by sorry
