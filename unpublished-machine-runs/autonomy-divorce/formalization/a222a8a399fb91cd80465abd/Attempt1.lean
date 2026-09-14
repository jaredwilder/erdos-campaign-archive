import Mathlib

open scoped BigOperators

/-- Any zero-sum linear relation is preserved by the reflection `x ↦ A - x`.
This is the reusable theorem behind the C_k reflection audit because every
alternating binomial coefficient vector has coefficient sum zero. -/
theorem zero_sum_reflection_invariant
    {m : Nat} (c x : Fin m → ℤ) (A : ℤ)
    (hc : ∑ i, c i = 0)
    (hx : ∑ i, c i * x i = 0) :
    ∑ i, c i * (A - x i) = 0 := by
  calc
    ∑ i, c i * (A - x i)
        = ∑ i, (c i * A - c i * x i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (∑ i, c i * A) - ∑ i, c i * x i := by
          rw [Finset.sum_sub_distrib]
    _ = A * (∑ i, c i) - ∑ i, c i * x i := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 0 := by rw [hc, hx]; ring

#print axioms zero_sum_reflection_invariant

#print axioms zero_sum_reflection_invariant
