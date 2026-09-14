import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open scoped Classical

abbrev msl_p_fx_geom (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i ≤ 2

abbrev msl_q_fx_geom_s1 (n : Nat) : Prop :=
  ∑ i ∈ Finset.range n, ((1 : ℚ) / 2) ^ i = 2 - 2 * ((1 : ℚ) / 2) ^ n
theorem msl_elab_probe : ∀ (n : Nat), msl_q_fx_geom_s1 n := by
  sorry
