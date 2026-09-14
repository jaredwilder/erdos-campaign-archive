import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos949_campaign_001_R014_L1_a2r1  : ∀ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → #Sᶜ = 𝔠 := by
  intro S hS
  obtain hS_lt | hS_eq : #S < 𝔠 ∨ #S = 𝔠 := lt_or_eq_of_le (by simpa using mk_set_le S)
  · rw [mk_compl_of_infinite, mk_real]
    exact hS_lt
  · have hSinf : S.Infinite := by
      simpa [hS_eq] using aleph0_le_continuum
    have hdouble : Function.Injective (fun x : ℝ => 2 * x) := by
      intro x y hxy
      linarith
    have hdouble_card : #(fun x : ℝ => 2 * x) '' S = 𝔠 := by
      rw [mk_image_eq hdouble, hS_eq]
    have hdouble_sub : (fun x : ℝ => 2 * x) '' S ⊆ Sᶜ := by
      intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      intro hmem
      exact hS a ha a ha (by simpa using hmem)
    apply le_antisymm
    · exact mk_set_le Sᶜ
    · rw [← hdouble_card]
      exact mk_subtype_mono hdouble_sub

-- axiom footprint
#print axioms msl_fmz_erdos949_campaign_001_R014_L1_a2r1
