import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators Nat

theorem p1 (n : ℕ) (x : ℝ) : (n : ℝ) + x = x + n := by ring
theorem p2 (S : Finset ℕ) : ∑ n ∈ S, (1:ℚ)/n = ∑ n ∈ S, (1:ℚ)/n := rfl
theorem p3 : Set.Infinite {k : ℕ | 2 ≤ k} → True := fun _ => trivial
theorem p4 (f : ℕ → ℝ) : Filter.Tendsto f Filter.atTop (nhds 0) → True := fun _ => trivial
theorem p5 (a b : ℕ) (h : 0 < b) : gcd a b ∣ a := Nat.gcd_dvd_left a b
theorem p6 (x : ℝ) (hx : 0 < x) : Real.log x = Real.log x := rfl
