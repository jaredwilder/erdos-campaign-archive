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
theorem th_t04_c2_base : msl_q_erdos289_b_m01_d1_s2 0 := by
  try simp only [msl_q_erdos289_b_m01_d1_s2, msl_p_erdos289_b_m01_d1] at *
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

#print axioms th_t04_c2_base
