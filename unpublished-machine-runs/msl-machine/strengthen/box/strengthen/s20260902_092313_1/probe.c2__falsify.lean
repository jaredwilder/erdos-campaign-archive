import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

abbrev msl_p_probe_geom (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i ≤ 2

abbrev msl_q_probe_geom_s2 (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i = 2 - ((1 : ℚ) / 2) ^ n

#eval (if (decide (msl_q_probe_geom_s2 0)) then "MSLF 0 TRUE" else "MSLF 0 FALSE")
#eval (if (decide (msl_q_probe_geom_s2 1)) then "MSLF 1 TRUE" else "MSLF 1 FALSE")
#eval (if (decide (msl_q_probe_geom_s2 2)) then "MSLF 2 TRUE" else "MSLF 2 FALSE")
