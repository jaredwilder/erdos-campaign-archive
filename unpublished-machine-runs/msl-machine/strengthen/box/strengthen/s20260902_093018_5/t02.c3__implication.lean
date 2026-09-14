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

abbrev msl_q_erdos289_a_m01_d2_s3 (n : Nat) : Prop :=
  ∀ m : Nat, m ≤ n → (2 ≤ m) → (m + 2 : Nat) < m * (m + 1)
theorem th_t02_c3_impl : ∀ (n : Nat), msl_q_erdos289_a_m01_d2_s3 n → msl_p_erdos289_a_m01_d2 n := by
  intro n h
  try simp only [msl_q_erdos289_a_m01_d2_s3, msl_p_erdos289_a_m01_d2] at *
  first
  | (trace "MSLCLOSE t01_decide"; set_option maxHeartbeats 1000 in (decide; done))
  | (trace "MSLCLOSE t02_omega"; set_option maxHeartbeats 3000 in (omega; done))
  | (trace "MSLCLOSE t03_ring_nf"; set_option maxHeartbeats 2000 in (ring_nf; done))
  | (trace "MSLCLOSE t04_ring"; set_option maxHeartbeats 2000 in (ring; done))
  | (trace "MSLCLOSE t05_linarith"; set_option maxHeartbeats 4000 in (linarith; done))
  | (trace "MSLCLOSE t06_nlinarith"; set_option maxHeartbeats 10000 in (nlinarith; done))
  | (trace "MSLCLOSE t07_gcongr"; set_option maxHeartbeats 4000 in (gcongr; done))
  | (trace "MSLCLOSE t08_positivity"; set_option maxHeartbeats 2000 in (positivity; done))
  | (trace "MSLCLOSE t09_aesop"; set_option maxHeartbeats 20000 in (aesop; done))
  | (trace "MSLCLOSE t10_simp"; set_option maxHeartbeats 20000 in (simp; done))
  | (trace "MSLGOAL_BEGIN"; trace_state; sorry)

#print axioms th_t02_c3_impl
