import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators Nat

def dsum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

theorem hdrprobe : dsum 1 1 = 1 := by sorry
