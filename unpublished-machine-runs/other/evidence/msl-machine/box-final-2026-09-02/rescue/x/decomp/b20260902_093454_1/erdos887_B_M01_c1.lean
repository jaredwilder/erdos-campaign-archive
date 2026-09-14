import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def rqs (n : Nat) : ℝ := (n : ℝ)^((1:ℝ)/2)

def rqp (n : Nat) : ℝ := (n : ℝ)^((1:ℝ)/4)

/-- Number of divisors of `n` lying in the canonical open window (√n, √n + C·n^(1/4)). -/
def winDiv (n : Nat) (C : ℝ) : Nat :=
  (Finset.filter (fun (d : Nat) => d ∣ n ∧ rqs n < (d : ℝ) ∧ (d : ℝ) < rqs n + C * rqp n)
    (Finset.Icc 1 n)).card

theorem msl_erdos887_b_m01_c1 (K : Nat) : ∃ (C : ℝ) (n : Nat), 0 < C ∧ K < winDiv n C := by sorry
