import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

abbrev msl_p_probe_geom (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i ≤ 2

abbrev msl_q_probe_geom_s1 (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i = 2 - 2 * ((1 : ℚ) / 2) ^ n
theorem th_probe_c1_step : ∀ (k : Nat), msl_q_probe_geom_s1 k → msl_q_probe_geom_s1 (k + 1) := by
  intro k h
  try simp only [msl_q_probe_geom_s1, msl_p_probe_geom] at *
  first
  | (trace "MSLCLOSE t01_decide"; set_option maxHeartbeats 1000 in (decide))
  | (trace "MSLCLOSE t02_omega"; set_option maxHeartbeats 3000 in (omega))
  | (trace "MSLCLOSE t03_ring_nf"; set_option maxHeartbeats 2000 in (ring_nf))
  | (trace "MSLCLOSE t04_ring"; set_option maxHeartbeats 2000 in (ring))
  | (trace "MSLCLOSE t05_linarith"; set_option maxHeartbeats 4000 in (linarith))
  | (trace "MSLCLOSE t06_nlinarith"; set_option maxHeartbeats 10000 in (nlinarith))
  | (trace "MSLCLOSE t07_gcongr"; set_option maxHeartbeats 4000 in (gcongr))
  | (trace "MSLCLOSE t08_positivity"; set_option maxHeartbeats 2000 in (positivity))
  | (trace "MSLCLOSE t09_aesop"; set_option maxHeartbeats 20000 in (aesop))
  | (trace "MSLCLOSE t10_simp"; set_option maxHeartbeats 20000 in (simp))
  | (trace "MSLGOAL_BEGIN"; trace_state; sorry)

#print axioms th_probe_c1_step
