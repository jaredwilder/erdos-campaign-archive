import Mathlib

set_option autoImplicit false



def L1Fragment : Prop := ∃ f₁ f₂ : ℕ → ℕ, f₁ 13 = 2 ∧ f₁ 37 = 3 ∧ f₁ 73 = 4 ∧ f₂ 13 = 2 ∧ f₂ 37 = 3 ∧ f₂ 73 = 4 ∧ f₁ 2 ≠ f₂ 2

theorem msl_fmz_erdos1055_campaign_001_R011_L1_a1r4  : L1Fragment := by
  let f₁ : ℕ → ℕ := fun n => if n = 13 then 2 else if n = 37 then 3 else if n = 73 then 4 else 0
  let f₂ : ℕ → ℕ := fun n => if n = 13 then 2 else if n = 37 then 3 else if n = 73 then 4 else 1
  refine ⟨f₁, f₂, ?_⟩
  norm_num [f₁, f₂]

-- axiom footprint
#print axioms L1Fragment
#print axioms msl_fmz_erdos1055_campaign_001_R011_L1_a1r4
