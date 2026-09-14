import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def HasDensity (s : Set Nat) (δ : ℝ) : Prop :=
  Filter.Tendsto (fun (n : Nat) => ((s ∩ Set.Iio n).ncard : ℝ)) Filter.atTop (nhds δ)

def ProductMap (d : Nat → Nat) (p : Nat × Nat) : Nat :=
  ∏ i ∈ Finset.Icc p.1 p.2, d i

theorem msl_erdos421_a_m01_c2 (d : Nat → Nat) (hmono : StrictMono d) (hd0 : 1 ≤ d 0) : HasDensity (Set.range d) 1 := by sorry
