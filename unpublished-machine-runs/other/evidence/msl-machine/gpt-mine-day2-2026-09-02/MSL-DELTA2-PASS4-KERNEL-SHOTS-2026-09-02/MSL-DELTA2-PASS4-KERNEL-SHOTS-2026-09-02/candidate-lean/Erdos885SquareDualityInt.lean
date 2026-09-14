import Mathlib

set_option autoImplicit false

/-- Integer square-duality core for the #885 factor-difference reformulation. -/
theorem erdos885_square_duality_int (n d : ℤ) :
    (∃ a : ℤ, n = a * (a + d)) ↔
      ∃ s : ℤ, s ^ 2 = d ^ 2 + 4 * n ∧ 2 ∣ s - d := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨2 * a + d, ?_, ?_⟩
    · ring
    · refine ⟨a, ?_⟩
      ring
  · rintro ⟨s, hs, hpar⟩
    rcases hpar with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    nlinarith [hs, ha]
