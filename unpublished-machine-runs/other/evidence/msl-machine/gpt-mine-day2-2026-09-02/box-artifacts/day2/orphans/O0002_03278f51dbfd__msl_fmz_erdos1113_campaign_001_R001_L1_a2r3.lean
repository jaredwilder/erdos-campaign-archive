import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos1113_campaign_001_R001_L1_a2r3  : (IsEmpty Empty ∧ IsEmpty Empty) ∧ (¬ Nonempty Empty ∧ ¬ Nonempty Empty) := by
  constructor
  · exact ⟨inferInstance, inferInstance⟩
  · constructor <;> intro h
    · exact nomatch h.some
    · exact nomatch h.some

-- axiom footprint
#print axioms msl_fmz_erdos1113_campaign_001_R001_L1_a2r3
