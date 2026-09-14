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

def HasDecomp (k : Nat) : Prop :=
  ∃ I : Fin k → Nat × Nat,
    (∀ i : Fin k, (I i).1 < (I i).2) ∧
    (∀ (i j : Fin k), i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
    ∑ i : Fin k, ∑ n ∈ Icc (I i).1 (I i).2, ((n : Nat)⁻¹ : Rat) = 1

def blockedResidue (k : Nat) : Prop := k % 6 = 2

abbrev msl_p_erdos289_b_m01_d1 (k : Nat) : Prop :=
  HasDecomp k → k % 6 ≠ 2

abbrev msl_q_erdos289_b_m01_d1_s2 (k : Nat) : Prop :=
  k % (6 : ℕ) = (2 : ℕ) → ¬ HasDecomp k
example : (∀ (k : Nat), msl_q_erdos289_b_m01_d1_s2 k) = (∀ (k : Nat), msl_p_erdos289_b_m01_d1 k) := by
  first
  | rfl
  | fail "MSL_NOT_DEFEQ"
