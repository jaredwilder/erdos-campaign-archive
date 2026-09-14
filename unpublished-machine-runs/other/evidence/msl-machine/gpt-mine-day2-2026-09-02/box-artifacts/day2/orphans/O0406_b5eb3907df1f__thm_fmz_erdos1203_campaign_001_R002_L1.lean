import Mathlib

set_option autoImplicit false



theorem R002_L1 (lo1 hi1 lo2 hi2 : Q)
    (h1 : (0:Q) ≤ lo1) (h2 : lo1 ≤ hi1) (h3 : (0:Q) ≤ lo2) (h4 : lo2 ≤ hi2) :
    (∀ x y : Q, lo1 ≤ x → x ≤ hi1 → lo2 ≤ y → y ≤ hi2 →
        lo1 * lo2 ≤ x * y ∧ x * y ≤ hi1 * hi2)
      ∧ (∀ w : Q, lo1 ≤ w → w ≤ hi1 → lo2 ≤ w → w ≤ hi2 →
            lo1 * lo2 ≤ w * w ∧ w * w ≤ hi1 * hi2)
      ∧ (lo1 ≤ lo1 ∧ lo1 ≤ hi1 ∧ lo2 ≤ lo2 ∧ lo2 ≤ hi2 ∧ lo1 * lo2 = lo1 * lo2)
      ∧ (hi1 ≤ hi1 ∧ lo1 ≤ hi1 ∧ hi2 ≤ hi2 ∧ lo2 ≤ hi2 ∧ hi1 * hi2 = hi1 * hi2) := by
  refine ⟨fun x y hx1 hx2 hy1 hy2 => ?_, fun w hw1 hw2 hw3 hw4 => ?_,
    ⟨le_rfl, h2, le_rfl, h4, rfl⟩, ⟨le_rfl, h2, le_rfl, h4, rfl⟩⟩
  · have hx0 : (0:Q) ≤ x := h1.trans hx1
    have hy0 : (0:Q) ≤ y := h3.trans hy1
    exact ⟨(mul_le_mul_of_nonneg_right hx1 h3).trans (mul_le_mul_of_nonneg_left hy1 hx0),
      (mul_le_mul_of_nonneg_right hx2 hy0).trans
        (mul_le_mul_of_nonneg_left hy2 (h1.trans h2))⟩
  · have hw0 : (0:Q) ≤ w := h1.trans hw1
    exact ⟨(mul_le_mul_of_nonneg_right hw1 h3).trans (mul_le_mul_of_nonneg_left hw3 hw0),
      (mul_le_mul_of_nonneg_right hw2 hw0).trans
        (mul_le_mul_of_nonneg_left hw4 (h1.trans h2))⟩

theorem msl_fmz_erdos1203_campaign_001_R002_L1  : ∀ lo1 hi1 lo2 hi2 : Q, (0:Q) ≤ lo1 → lo1 ≤ hi1 → (0:Q) ≤ lo2 → lo2 ≤ hi2 →
  (∀ x y : Q, lo1 ≤ x → x ≤ hi1 → lo2 ≤ y → y ≤ hi2 →
      lo1 * lo2 ≤ x * y ∧ x * y ≤ hi1 * hi2)
  ∧ (∀ w : Q, lo1 ≤ w → w ≤ hi1 → lo2 ≤ w → w ≤ hi2 →
        lo1 * lo2 ≤ w * w ∧ w * w ≤ hi1 * hi2)
  ∧ (lo1 ≤ lo1 ∧ lo1 ≤ hi1 ∧ lo2 ≤ lo2 ∧ lo2 ≤ hi2 ∧ lo1 * lo2 = lo1 * lo2)
  ∧ (hi1 ≤ hi1 ∧ lo1 ≤ hi1 ∧ hi2 ≤ hi2 ∧ lo2 ≤ hi2 ∧ hi1 * hi2 = hi1 * hi2) := by
  refine ⟨fun x y hx1 hx2 hy1 hy2 => ?_, fun w hw1 hw2 hw3 hw4 => ?_,
    ⟨le_rfl, h2, le_rfl, h4, rfl⟩, ⟨le_rfl, h2, le_rfl, h4, rfl⟩⟩
  · have hx0 : (0:Q) ≤ x := h1.trans hx1
    have hy0 : (0:Q) ≤ y := h3.trans hy1
    exact ⟨(mul_le_mul_of_nonneg_right hx1 h3).trans (mul_le_mul_of_nonneg_left hy1 hx0),
      (mul_le_mul_of_nonneg_right hx2 hy0).trans
        (mul_le_mul_of_nonneg_left hy2 (h1.trans h2))⟩
  · have hw0 : (0:Q) ≤ w := h1.trans hw1
    exact ⟨(mul_le_mul_of_nonneg_right hw1 h3).trans (mul_le_mul_of_nonneg_left hw3 hw0),
      (mul_le_mul_of_nonneg_right hw2 hw0).trans
        (mul_le_mul_of_nonneg_left hw4 (h1.trans h2))⟩

-- axiom footprint
#print axioms R002_L1
#print axioms msl_fmz_erdos1203_campaign_001_R002_L1
