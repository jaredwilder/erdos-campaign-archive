import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos1113_campaign_001_R001_L1_a2r4  : IsEmpty Empty ∧ IsEmpty Empty ∧ ¬ Nonempty Empty ∧ ¬ Nonempty Empty := by
  constructor
  · exact inferInstance
  constructor
  · exact inferInstance
  constructor
  · intro h
    exact nomatch h.some
  · intro h
    exact nomatch h.some

-- axiom footprint
#print axioms msl_fmz_erdos1113_campaign_001_R001_L1_a2r4
