import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

abbrev msl_p_probe_geom (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i ≤ 2

abbrev msl_q_probe_geom_s1 (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i = 2 - 2 * ((1 : ℚ) / 2) ^ n
theorem msl_elab_probe : ∀ (n : Nat), msl_q_probe_geom_s1 n := by
  sorry
