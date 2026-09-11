/-
THE IRRATIONALITY BLADE — denominator-bound criterion.
Reusable core for Erdos #243, #247, #249, #251, #257, #260, #1049, #68.
Self-contained; depends on Mathlib only.
-/
import Mathlib

namespace IrrationalityBlade

/-- **THE BLADE.**  If for every positive `q` one can produce a natural `D` and an
integer `P` with `0 < D*x - P` and `q*(D*x - P) < 1`, then `x` is irrational.
The hypothesis manufactures an integer strictly between `0` and `1` out of any
rational representation of `x`. -/
theorem irrational_of_denominator_squeeze (x : ℝ)
    (h : ∀ q : ℕ, 0 < q →
      ∃ (D : ℕ) (P : ℤ), 0 < (D : ℝ) * x - (P : ℝ) ∧
        (q : ℝ) * ((D : ℝ) * x - (P : ℝ)) < 1) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨D, P, h1, h2⟩ := h r.den r.pos
  have hden : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.pos
  set y : ℚ := (D : ℚ) * r - (P : ℚ) with hy
  have hy1 : (0 : ℚ) < y := by
    have hR : (0 : ℝ) < ((y : ℚ) : ℝ) := by push_cast [hy]; exact h1
    exact_mod_cast hR
  have hy2 : (r.den : ℚ) * y < 1 := by
    have hR : ((((r.den : ℚ) * y : ℚ)) : ℝ) < ((1 : ℚ) : ℝ) := by push_cast [hy]; exact h2
    exact_mod_cast hR
  have hnum : (r.den : ℚ) * r = (r.num : ℚ) := by
    rw [mul_comm]; exact Rat.mul_den_eq_num r
  set k : ℤ := (D : ℤ) * r.num - (r.den : ℤ) * P with hk
  have hkq : (k : ℚ) = (r.den : ℚ) * y := by
    push_cast [hk, hy]
    rw [← hnum]; ring
  have hkgt : (0 : ℚ) < (k : ℚ) := by rw [hkq]; exact mul_pos hden hy1
  have hklt : (k : ℚ) < 1 := by rw [hkq]; exact hy2
  have h0 : 0 < k := by exact_mod_cast hkgt
  have h1' : k < 1 := by exact_mod_cast hklt
  omega

/-- Blade, tail form: a family of head-clearing multipliers indexed by `m`. -/
theorem irrational_of_head_clearing
    (x : ℝ) (D : ℕ → ℕ) (P : ℕ → ℤ)
    (hpos : ∀ m, 0 < (D m : ℝ) * x - (P m : ℝ))
    (hsmall : ∀ q : ℕ, 0 < q → ∃ m, (q : ℝ) * ((D m : ℝ) * x - (P m : ℝ)) < 1) :
    Irrational x := by
  refine irrational_of_denominator_squeeze x fun q hq => ?_
  obtain ⟨m, hm⟩ := hsmall q hq
  exact ⟨D m, P m, hpos m, hm⟩

end IrrationalityBlade

#print axioms IrrationalityBlade.irrational_of_denominator_squeeze
#print axioms IrrationalityBlade.irrational_of_head_clearing
