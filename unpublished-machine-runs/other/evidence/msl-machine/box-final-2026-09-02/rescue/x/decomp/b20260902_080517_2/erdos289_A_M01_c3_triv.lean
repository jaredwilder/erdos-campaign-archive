import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset

-- campaign vocabulary, already kernel-checked (msl_decompose)
def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n

def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

-- proposed definitions

theorem msl_erdos289_a_m01_c3_triv : ∀ᶠ k : ℕ in Filter.atTop, ∃ J : Fin k → ℕ × ℕ, (∀ (i : Fin k), 5 ≤ (J i).1 ∧ (J i).1 < (J i).2) ∧ (∀ (i j : Fin k), i ≠ j → (J i).2 < (J j).1 ∨ (J j).2 < (J i).1) ∧ ∑ i, ∑ n ∈ Icc (J i).1 (J i).2, ((n : ℚ)⁻¹) = (1 : ℚ) / 6 := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
