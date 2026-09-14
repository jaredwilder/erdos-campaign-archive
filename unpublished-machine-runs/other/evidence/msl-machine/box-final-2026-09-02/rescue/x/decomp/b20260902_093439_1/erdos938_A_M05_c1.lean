import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def apStart (k : Nat) : Prop :=
  ((nth Powerful k : Nat) : ℤ) + ((nth Powerful (k + 2) : Nat) : ℤ) = 2 * ((nth Powerful (k + 1) : Nat) : ℤ)

def apStarts : Set Nat := {k : Nat | apStart k}

theorem msl_erdos938_a_m05_c1 (k : Nat) : apStart k ↔ ((nth Powerful (k + 1) : Nat) : ℤ) - (nth Powerful k : Nat) = ((nth Powerful (k + 2) : Nat) : ℤ) - (nth Powerful (k + 1) : Nat) := by sorry
