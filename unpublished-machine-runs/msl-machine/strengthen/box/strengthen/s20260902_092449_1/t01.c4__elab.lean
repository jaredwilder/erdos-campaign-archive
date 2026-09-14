import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

-- campaign vocabulary, already kernel-checked (msl_decompose)
def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n

def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

-- proposed definitions

abbrev msl_p_erdos289_a_m01_d1 (n : Nat) : Prop :=
  2 ≤ n → ((1 : ℚ) / n = (1 : ℚ) / (n + 1) + (1 : ℚ) / (n * (n + 1)))

abbrev msl_q_erdos289_a_m01_d1_s4 (n : Nat) : Prop :=
  ((2 ≤ n → (1 : ℚ) / n = (1 : ℚ) / (n + 1) + (1 : ℚ) / (n * (n + 1))) ∧ (1 ≤ n → (n : ℚ) ≠ 0 ∧ (1 : ℚ) / n ≤ (1 : ℚ)))
theorem msl_elab_probe : ∀ (n : Nat), msl_q_erdos289_a_m01_d1_s4 n := by
  sorry
