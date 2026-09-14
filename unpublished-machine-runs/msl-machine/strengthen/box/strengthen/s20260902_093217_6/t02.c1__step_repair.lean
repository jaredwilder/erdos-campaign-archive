import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

-- campaign vocabulary, already kernel-checked (msl_decompose)
def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n

def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

-- proposed definitions

abbrev msl_p_erdos289_a_m01_d2 (n : Nat) : Prop :=
  2 ≤ n → (n + 1) + 1 < n * (n + 1)

abbrev msl_q_erdos289_a_m01_d2_s1 (n : Nat) : Prop :=
  (2 ≤ n) → (n * (n + 1) : Nat) = (n + 2) + (n * n - 2)
theorem th_t02_c1_step : ∀ (k : Nat), msl_q_erdos289_a_m01_d2_s1 k → msl_q_erdos289_a_m01_d2_s1 (k + 1) := by
  intro k h
  try simp only [msl_q_erdos289_a_m01_d2_s1, msl_p_erdos289_a_m01_d2] at *
  intro k h
  simp only [msl_q_erdos289_a_m01_d2_s1] at h ⊢
  intro h2
  ring

#print axioms th_t02_c1_step
