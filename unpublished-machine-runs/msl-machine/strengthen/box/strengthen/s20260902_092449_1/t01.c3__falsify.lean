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

abbrev msl_q_erdos289_a_m01_d1_s3 (n : Nat) : Prop :=
  (∀ m ≤ n, 2 ≤ m → (1 : ℚ) / m = (1 : ℚ) / (m + 1) + (1 : ℚ) / (m * (m + 1)))

#eval (if (decide (msl_q_erdos289_a_m01_d1_s3 0)) then "MSLF 0 TRUE" else "MSLF 0 FALSE")
#eval (if (decide (msl_q_erdos289_a_m01_d1_s3 1)) then "MSLF 1 TRUE" else "MSLF 1 FALSE")
#eval (if (decide (msl_q_erdos289_a_m01_d1_s3 2)) then "MSLF 2 TRUE" else "MSLF 2 FALSE")
