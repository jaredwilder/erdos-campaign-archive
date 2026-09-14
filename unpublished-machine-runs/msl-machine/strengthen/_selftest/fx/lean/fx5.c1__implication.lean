import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open scoped Classical

abbrev msl_p_fx_geom (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i ≤ 2

abbrev msl_q_fx_geom_s1 (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i = 2 - 2 * ((1 : ℚ) / 2) ^ n
theorem th_fx5_c1_impl : ∀ (n : Nat), msl_q_fx_geom_s1 n → msl_p_fx_geom n := by
  intro n h
  try simp only [msl_q_fx_geom_s1, msl_p_fx_geom] at *
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

#print axioms th_fx5_c1_impl
