import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def feasiblePair (n a b : Nat) : Prop := a.factorial * b.factorial ∣ n.factorial

def excessAtLeast1 (n a b : Nat) : Prop := a + b ≥ n + 1

def witnessPair (n : Nat) : Nat × Nat := (n, 1)

def smallRange : Finset Nat := Finset.Icc (2 : Nat) (200 : Nat)

theorem msl_erdos400_lem_r008_l1_g2_small_range_c3 (n : Nat) : n ∈ smallRange → 2 ≤ n := by sorry
