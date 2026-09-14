import Mathlib

set_option autoImplicit false


set_option maxHeartbeats 800000

theorem msl_erdos313_finite_a1  : Set.Finite {p : ℕ | Nat.Prime p ∧ (p - 6) ∣ 36} := by
  refine Set.Finite.subset (Finset.range 43).finite_toSet ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have hle : p - 6 ≤ 36 := Nat.le_of_dvd (by norm_num) hp.2
  simp only [Finset.mem_coe, Finset.mem_range]
  omega

-- axiom footprint
#print axioms msl_erdos313_finite_a1
