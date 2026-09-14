import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset
open Filter

-- campaign vocabulary, already kernel-checked (msl_decompose)
def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n

def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

-- proposed definitions

def goodFamily (k : Nat) (I : Fin k → Nat × Nat) : Prop :=
  (∀ i : Fin k, (I i).1 < (I i).2) ∧
  (∀ (i j : Fin k), i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
  (∑ i : Fin k, ∑ n ∈ Icc (I i).1 (I i).2, ((n : Nat)⁻¹ : Rat)) = 1

def familyPredicate (k : Nat) : Prop :=
  ∃ I : Fin k → Nat × Nat, goodFamily k I
