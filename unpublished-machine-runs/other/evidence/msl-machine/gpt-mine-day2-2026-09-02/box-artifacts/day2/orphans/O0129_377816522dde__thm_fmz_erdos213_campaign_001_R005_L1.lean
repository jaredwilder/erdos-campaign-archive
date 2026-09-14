import Mathlib

set_option autoImplicit false



namespace Erdos213L1

/-- Fail-closed integer cross-multiplication acceptance predicate: no floating point
anywhere; aborts (returns false) on any zero denominator BEFORE any comparison. -/
def accept (xNum xDen tNum tDen : ℤ) : Bool :=
  if xDen = 0 ∨ tDen = 0 then false
  else decide (xNum.natAbs * tDen.natAbs ≤ tNum.natAbs * xDen.natAbs)

end Erdos213L1

theorem msl_fmz_erdos213_campaign_001_R005_L1  : Erdos213L1.accept_abort :
  ∀ (xNum xDen tNum tDen : ℤ), xDen = 0 ∨ tDen = 0 →
    Erdos213L1.accept xNum xDen tNum tDen = false

Erdos213L1.accept_iff :
  ∀ (xNum xDen tNum tDen : ℤ), xDen ≠ 0 → tDen ≠ 0 →
    (Erdos213L1.accept xNum xDen tNum tDen = true ↔
      |(xNum : ℚ) / xDen| ≤ |(tNum : ℚ) / tDen|)

Erdos213L1.accept_boundary :
  ∀ (xNum xDen tNum tDen : ℤ), xDen ≠ 0 → tDen ≠ 0 →
    xNum.natAbs * tDen.natAbs = tNum.natAbs * xDen.natAbs →
    Erdos213L1.accept xNum xDen tNum tDen = true := by
  intro xNum xDen tNum tDen h
  exact if_pos h

by
  intro xNum xDen tNum tDen hxd htd
  have hnc : ¬(xDen = 0 ∨ tDen = 0) := by
    rintro (h0 | h0)
    · exact hxd h0
    · exact htd h0
  have hbx : (0:ℚ) < |(xDen : ℚ)| := by
    rw [abs_pos_iff]
    simpa using hxd
  have hbt : (0:ℚ) < |(tDen : ℚ)| := by
    rw [abs_pos_iff]
    simpa using htd
  unfold accept
  rw [if_neg hnc, decide_eq_true_eq]
  rw [abs_div, abs_div, Int.cast_abs, Int.cast_abs, Int.cast_abs, Int.cast_abs]
  rw [div_le_div_iff hbx hbt, ← Int.cast_mul, ← Int.cast_mul, Int.cast_le]
  conv_lhs =>
    rw [← Int.abs_eq_natAbs xNum]
  conv_rhs =>
    rw [← Int.abs_eq_natAbs tNum]
  have hs : ∀ (u v : ℤ), (|u| * |v| : ℤ) = (|u| * |v| : ℤ) := fun _ _ => rfl
  have hsign : ∀ (u v : ℤ), (|u| : ℤ) * |v| = (u.natAbs : ℤ) * v.natAbs := by
    intro u v
    rw [Int.abs_eq_natAbs u, Int.abs_eq_natAbs v]
  rw [hsign xNum tDen, hsign tNum xDen]
  exact Iff.rfl

by
  intro xNum xDen tNum tDen hxd htd heq
  unfold accept
  have hnc : ¬(xDen = 0 ∨ tDen = 0) := by
    rintro (h0 | h0)
    · exact hxd h0
    · exact htd h0
  rw [if_neg hnc]
  exact decide_eq_true (le_of_eq heq)

-- axiom footprint
#print axioms Erdos213L1.accept
#print axioms msl_fmz_erdos213_campaign_001_R005_L1
