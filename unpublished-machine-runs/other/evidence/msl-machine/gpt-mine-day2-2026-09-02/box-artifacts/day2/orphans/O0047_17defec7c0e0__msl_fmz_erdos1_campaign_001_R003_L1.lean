import Mathlib

set_option autoImplicit false



-- Fail-closed, float-free exact rational comparison by cross-multiplied
-- integer arithmetic: `none` = aborted (unresolved sign, zero denominator).
def exactCompare (a b c d : ℤ) : Option Bool :=
  if b = 0 ∨ d = 0 then none
  else if 0 < b * d then some (decide (a * d < c * b))
  else some (decide (c * b < a * d))

private lemma div_sign (x c : ℚ) (hc : c ≠ 0) :
    x / c < 0 ↔ (0 < c ∧ x < 0) ∨ (c < 0 ∧ 0 < x) := by
  rcases lt_trichotomy 0 c with h0 | h0 | h0
  · rw [div_lt_iff h0, zero_mul]
    exact ⟨fun h => Or.inl ⟨h0, h⟩, fun ⟨_, h⟩ => h⟩
  · exact absurd h0.symm hc
  · rw [div_lt_iff_of_neg h0, zero_mul]
    exact ⟨fun h => Or.inr ⟨h0, h⟩, fun ⟨_, h⟩ => h⟩

private lemma cross_char (a b c d : ℚ) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b < c / d ↔ (if 0 < b * d then a * d < c * b else c * b < a * d) := by
  have hbz : b * d ≠ 0 := mul_ne_zero hb hd
  have hsplit : a / b - c / d = (a * d - c * b) / (b * d) := by
    field_simp
  conv_lhs => rw [← sub_lt_zero]
  rw [hsplit, div_sign (a * d - c * b) (b * d) hbz, sub_lt_zero, sub_pos]
  by_cases h : 0 < b * d
  · simp [h]
  · have hneg : b * d < 0 := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hbz)
    simp [h, hneg]

theorem msl_fmz_erdos1_campaign_001_R003_L1  : theorem L1_full (a b c d : ℤ) :
    (b = 0 ∨ d = 0 → exactCompare a b c d = none) ∧
    exactCompare a b c d = exactCompare a b c d ∧
    (b ≠ 0 → d ≠ 0 → ∃ v : Bool, exactCompare a b c d = some v ∧
      (v = true ↔ (a:ℚ) / (b:ℚ) < (c:ℚ) / (d:ℚ))) := by
  have hfail : ∀ a b c d : ℤ, b = 0 ∨ d = 0 → exactCompare a b c d = none := by
    intro a b c d h
    rcases h with h | h
    · simp [exactCompare, h]
    · simp [exactCompare, h]
  refine ⟨hfail a b c d, rfl, ?_⟩
  intro hb hd
  have hQb : (b:ℚ) ≠ 0 := by exact_mod_cast hb
  have hQd : (d:ℚ) ≠ 0 := by exact_mod_cast hd
  have hQsign : (0:ℚ) < (b:ℚ) * (d:ℚ) ↔ 0 < b * d := by
    rw [show (b:ℚ) * (d:ℚ) = ((b * d : ℤ) : ℚ) by rw [Int.cast_mul]]
    exact Int.cast_lt
  have hchar := cross_char (a:ℚ) (b:ℚ) (c:ℚ) (d:ℚ) hQb hQd
  unfold exactCompare
  split_ifs with h0 hsign
  · rcases h0 with h | h
    · exact absurd h hb
    · exact absurd h hd
  · refine ⟨decide (a * d < c * b), rfl, ?_⟩
    rw [hchar, if_pos (hQsign.mpr hsign), ← Int.cast_mul, ← Int.cast_mul,
        Int.cast_lt, Int.cast_lt]
    exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩
  · have hneg : b * d < 0 :=
      lt_of_le_of_ne (le_of_not_gt hsign) (Ne.symm (mul_ne_zero hb hd))
    refine ⟨decide (c * b < a * d), rfl, ?_⟩
    rw [hchar, if_neg (fun hc => hsign (hQsign.mp hc)), ← Int.cast_mul, ← Int.cast_mul,
        Int.cast_lt, Int.cast_lt]
    exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

-- axiom footprint
#print axioms exactCompare
#print axioms div_sign
#print axioms cross_char
#print axioms msl_fmz_erdos1_campaign_001_R003_L1
