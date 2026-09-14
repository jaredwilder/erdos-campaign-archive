import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos949_campaign_001_R014_L1_a2r3  : ∀ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → #Sᶜ = 𝔠 := by
  intro S hS
  obtain hS_lt | hS_eq : #S < 𝔠 ∨ #S = 𝔠 :=
    lt_or_eq_of_le (by simpa using mk_set_le S)
  · rw [mk_compl_of_infinite, mk_real]
    exact hS_lt
  · have hdouble : Function.Injective (fun x : ℝ => x + x) := by
      intro x y hxy
      linarith
    have hdouble_image : #(fun x : ℝ => x + x) '' S = 𝔠 := by
      rw [mk_image_eq hdouble, hS_eq]
    have hdouble_subset : (fun x : ℝ => x + x) '' S ⊆ Sᶜ := by
      intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      simpa only [Set.mem_compl_iff] using hS a ha a ha
    apply le_antisymm
    · exact mk_set_le Sᶜ
    · rw [← hdouble_image]
      exact mk_subtype_mono hdouble_subset

-- axiom footprint
#print axioms msl_fmz_erdos949_campaign_001_R014_L1_a2r3
