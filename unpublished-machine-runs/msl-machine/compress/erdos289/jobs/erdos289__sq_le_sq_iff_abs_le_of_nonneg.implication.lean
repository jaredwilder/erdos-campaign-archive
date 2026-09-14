import Mathlib
set_option autoImplicit false
def l1_statement : Prop := ∀ (R B : ℚ), 0 ≤ B → (R ^ 2 ≤ B ^ 2 ↔ |R| ≤ B)
-- no auxiliary definitions
set_option maxHeartbeats 400000

-- THE NORMALIZATION PRELUDE (msl_ladder, deterministic, $0).
-- The claim it tests: most leaf failures on an arithmetic DAG are SIDE-CONDITIONS
-- (an un-introduced hypothesis, a numeric coercion, a nonnegativity obligation),
-- not mathematics.  Each step is `try`, so the prelude never fails and never
-- changes what a tactic after it is allowed to prove.
macro "msl_prelude" : tactic =>
  `(tactic| ((try intros); (try push_cast); (try positivity)))

-- ---- children, INCLUDED BY SOURCE (each already PROVED_KERNEL alone)
theorem msl_fmz_erdos289_campaign_001_R006_L1_a2r4 l1_statement := by
  first
  | decide
  | norm_num
  | simp

theorem msl_fmz_erdos289_campaign_001_R006_L1_a2r3 ∀ R B : ℚ, (0 ≤ B ∧ R ^ 2 ≤ B ^ 2) ↔ (0 ≤ B ∧ |R| ≤ B) := by
  first
  | decide
  | norm_num
  | simp

-- ---- the composition: children -> parent
theorem sq_le_sq_iff_abs_le_of_nonneg_composition {α : Type*} [LinearOrderedField α] (R B : α) : ((msl_fmz_erdos289_campaign_001_R006_L1_a2r4 : l1_statement) ∧ (msl_fmz_erdos289_campaign_001_R006_L1_a2r3 : ∀ $v1 $v0 : ℚ, (0 ≤ $v0 ∧ $v1 ^ 2 ≤ $v0 ^ 2) ↔ (0 ≤ $v0 ∧ |$v1| ≤ $v0))) → (0 ≤ B → (R ^ 2 ≤ B ^ 2 ↔ |R| ≤ B)) := by
  first
  | (decide; done)
  | (omega; done)
  | (norm_num; done)
  | (ring_nf; done)
  | (ring_nf; ring; done)
  | (linarith; done)
  | (nlinarith; done)
  | (positivity; done)
  | (gcongr; done)
  | (simp_all; done)
  | (aesop; done)
  | (msl_prelude; done)
  | (msl_prelude; omega; done)
  | (msl_prelude; norm_num; done)
  | (msl_prelude; linarith; done)
  | (msl_prelude; nlinarith; done)
  | (msl_prelude; ring_nf; done)
  | (msl_prelude; ring_nf; ring; done)
  | (msl_prelude; decide; done)
  | (msl_prelude; simp_all; done)
  | (msl_prelude; aesop; done)
  | (msl_prelude; field_simp; done)
  | (msl_prelude; field_simp; ring; done)
  | (msl_prelude; qify; omega; done)

-- ---- the parent, by exact application of the composition
theorem sq_le_sq_iff_abs_le_of_nonneg {α : Type*} [LinearOrderedField α] (R B : α) : 0 ≤ B → (R ^ 2 ≤ B ^ 2 ↔ |R| ≤ B) := by
  first
  | exact sq_le_sq_iff_abs_le_of_nonneg_composition ⟨msl_fmz_erdos289_campaign_001_R006_L1_a2r4, msl_fmz_erdos289_campaign_001_R006_L1_a2r3⟩
  | (apply sq_le_sq_iff_abs_le_of_nonneg_composition; exact ⟨msl_fmz_erdos289_campaign_001_R006_L1_a2r4, msl_fmz_erdos289_campaign_001_R006_L1_a2r3⟩)
  | (intros; exact sq_le_sq_iff_abs_le_of_nonneg_composition ⟨msl_fmz_erdos289_campaign_001_R006_L1_a2r4, msl_fmz_erdos289_campaign_001_R006_L1_a2r3⟩)

#print axioms sq_le_sq_iff_abs_le_of_nonneg_composition
#print axioms sq_le_sq_iff_abs_le_of_nonneg
