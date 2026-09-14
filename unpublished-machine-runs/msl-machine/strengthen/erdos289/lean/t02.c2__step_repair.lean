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

abbrev msl_q_erdos289_a_m01_d2_s2 (n : Nat) : Prop :=
  (2 ≤ n) → ((n + 2 : Nat) < n * (n + 1) ∧ 4 ≤ n * n)
theorem th_t02_c2_step : ∀ (k : Nat), msl_q_erdos289_a_m01_d2_s2 k → msl_q_erdos289_a_m01_d2_s2 (k + 1) := by
  intro k h
  try simp only [msl_q_erdos289_a_m01_d2_s2, msl_p_erdos289_a_m01_d2] at *
  intro k h
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> omega
  · obtain ⟨ha, hb⟩ := h hk
    constructor
    · nlinarith
    · nlinarith

#print axioms th_t02_c2_step
