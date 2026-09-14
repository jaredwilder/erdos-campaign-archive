import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos949_campaign_001_R014_L1_a2r5  : ∀ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → #Sᶜ = 𝔠 := by
  intro S hsum
  by_cases hSc : #S < 𝔠
  · rw [mk_compl_of_infinite, mk_real]
    exact hSc
  · have hSc' : #S = 𝔠 := by
      exact le_antisymm (by simpa using mk_set_le S) (not_lt.mp hSc)
    let f : ℝ → ℝ := fun x => x + x
    have hf : Function.Injective f := by
      intro x y hxy
      dsimp [f] at hxy
      linarith
    have himage : #(f '' S) = 𝔠 := by
      rw [Cardinal.mk_image_eq hf, hSc']
    have hsub : f '' S ⊆ Sᶜ := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hsum x hx x hx
    have hle : 𝔠 ≤ #Sᶜ := by
      rw [← himage]
      exact mk_subtype_mono hsub
    exact le_antisymm (by simpa using mk_set_le Sᶜ) hle

-- axiom footprint
#print axioms msl_fmz_erdos949_campaign_001_R014_L1_a2r5
