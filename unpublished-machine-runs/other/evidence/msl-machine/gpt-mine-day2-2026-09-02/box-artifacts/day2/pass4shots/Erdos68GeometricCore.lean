import Mathlib

set_option autoImplicit false

/-- Finite geometric identity used by the #68 reciprocal-factorial expansion. -/
theorem erdos68_geometric_core (N : ℤ) : ∀ k : ℕ,
    (N - 1) * (∑ i ∈ Finset.range k, N ^ i) = N ^ k - 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      rw [mul_add, ih, pow_succ]
      ring

-- axiom footprint
#print axioms erdos68_geometric_core
