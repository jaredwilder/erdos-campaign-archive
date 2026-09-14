import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset
open Filter

def PairwiseSep (k : Nat) (I : Fin k → ℕ × ℕ) : Prop :=
  ∀ (i j : Fin k), i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1

def SizeAtLeast2 (k : Nat) (I : Fin k → ℕ × ℕ) : Prop :=
  ∀ (i : Fin k), (I i).1 < (I i).2

def StartsAbove (k : Nat) (m : Nat) (I : Fin k → ℕ × ℕ) : Prop :=
  ∀ (i : Fin k), m ≤ (I i).1

def RunSumQ (k : Nat) (I : Fin k → ℕ × ℕ) : ℚ :=
  ∑ i : Fin k, ∑ n ∈ Icc (I i).1 (I i).2, ((n : ℕ) : ℚ)⁻¹

def TailScheme (k : Nat) (I : Fin k → ℕ × ℕ) : Prop :=
  SizeAtLeast2 k I ∧ PairwiseSep k I ∧ StartsAbove k 5 I ∧ RunSumQ k I = (1 : ℚ) / 6

def FullScheme (k : Nat) (I : Fin k → ℕ × ℕ) : Prop :=
  SizeAtLeast2 k I ∧ PairwiseSep k I ∧ RunSumQ k I = (1 : ℚ)

def TailWitness (k : Nat) : Prop := ∃ (I : Fin k → ℕ × ℕ), TailScheme k I

def FullWitness (k : Nat) : Prop := ∃ (I : Fin k → ℕ × ℕ), FullScheme k I

theorem msl_erdos289_a_m01_c2 (k : Nat) : (1 : ℚ) / 2 + (1 : ℚ) / 3 + (1 : ℚ) / 6 = (1 : ℚ) ∧ (2 : ℕ) < 3 ∧ 3 < 5 := by sorry
