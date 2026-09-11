import Mathlib
import Attack01

/-!
# Erdős 949 — the covering reduction and the transfer principle

Builds on `Attack01` (same campaign).

* `witness_of_no_small_cover` : **the main new reduction.** If `ℝ` is NOT the union of fewer
  than continuum many translates of `S ∪ S/2`, then Erdős 949 holds for `S`.
  This strictly generalises the recorded `#S < 𝔠` case (a set of size `< 𝔠` cannot cover `ℝ`
  with `< 𝔠` translates), and it is what confines the open problem to *translation-large*
  sum-free sets.
* `witness_of_mk_lt_continuum'` : the recorded case, re-derived from the reduction.
* `witness_of_preimage` : **transfer principle.** `Witness` pulls back along any injective
  additive map `φ : ℝ →+ ℝ`: if the conclusion holds for `φ ⁻¹' S` it holds for `S`.
  So one may WLOG restrict `S` to any `ℚ`-subspace of dimension `𝔠`.
* `witness_of_addClosed` : any continuum-sized additively closed set avoiding `S` is a witness.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Cardinal MeasureTheory
open scoped Pointwise Cardinal Topology

namespace Erdos949Close

variable {S : Set ℝ}

/-- The translates of `Y` by the elements of `T` cover `ℝ`. -/
def TranslatesCover (Y T : Set ℝ) : Prop := ∀ x : ℝ, ∃ t ∈ T, x - t ∈ Y

/-- **Covering reduction.** If `ℝ` cannot be covered by fewer than continuum many translates
of `S ∪ S/2`, then Erdős 949 holds for `S`. -/
theorem witness_of_no_small_cover (S : Set ℝ)
    (h : ∀ T : Set ℝ, #T < 𝔠 → ¬ TranslatesCover (S ∪ ((fun x => 2 * x) ⁻¹' S)) T) :
    Witness S := by
  classical
  obtain ⟨A, hAS, hAA, hcov⟩ := exists_maximal_partial S
  refine ⟨A, hAS, ?_, Set.add_subset_iff.2 hAA⟩
  by_contra hne
  have hAle : #A ≤ 𝔠 := (Cardinal.mk_set_le A).trans_eq Cardinal.mk_real
  have hA𝔠 : #A < 𝔠 := lt_of_le_of_ne hAle hne
  have hcover := cover_of_maximal (S := S) hcov
  rcases Set.eq_empty_or_nonempty (S ∪ ((fun x => 2 * x) ⁻¹' S)) with hY | ⟨y₀, hy₀⟩
  · -- `S` is empty: then the maximal set is everything, contradicting `#A < 𝔠`.
    have hSe : S = ∅ := Set.eq_empty_of_subset_empty (hY ▸ Set.subset_union_left)
    have huniv : (univ : Set ℝ) ⊆ A := by
      intro x hx
      rcases hcover hx with ((hx1 | hx2) | hx3) | hx4
      · exact absurd hx1 (by rw [hSe]; exact fun h => h)
      · exact absurd hx2 (by rw [hSe]; exact fun h => h)
      · exact hx3
      · obtain ⟨a, _, hxa⟩ := Set.mem_iUnion₂.1 hx4
        exact absurd hxa (by rw [hSe]; exact fun h => h)
    have : (𝔠 : Cardinal) ≤ #A := by
      calc (𝔠 : Cardinal) = #(univ : Set ℝ) := by rw [Cardinal.mk_univ, Cardinal.mk_real]
        _ ≤ #A := Cardinal.mk_le_mk_of_subset huniv
    exact absurd (this.trans_lt hA𝔠) (lt_irrefl _)
  · -- Otherwise the maximal set yields `< 𝔠` translates covering `ℝ`.
    set T : Set ℝ := insert 0 (((fun a => -a) '' A) ∪ ((fun a => a - y₀) '' A)) with hT
    have hTcard : #T < 𝔠 := by
      have h1 : #(((fun a => -a) '' A) ∪ ((fun a => a - y₀) '' A) : Set ℝ) ≤ #A + #A :=
        le_trans (Cardinal.mk_union_le _ _) (add_le_add Cardinal.mk_image_le Cardinal.mk_image_le)
      have h2 : #T ≤ (#A + #A) + 1 := le_trans (Cardinal.mk_insert_le) (add_le_add h1 le_rfl)
      refine h2.trans_lt ?_
      refine Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum
        (Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum hA𝔠 hA𝔠) ?_
      exact one_lt_aleph0.trans_le Cardinal.aleph0_le_continuum
    refine h T hTcard ?_
    intro x
    rcases hcover (Set.mem_univ x) with ((hx1 | hx2) | hx3) | hx4
    · exact ⟨0, Set.mem_insert _ _, by simpa using Or.inl hx1⟩
    · exact ⟨0, Set.mem_insert _ _, by simpa using Or.inr hx2⟩
    · refine ⟨x - y₀, Set.mem_insert_of_mem _ (Or.inr ⟨x, hx3, rfl⟩), ?_⟩
      have : x - (x - y₀) = y₀ := by ring
      rw [this]
      exact hy₀
    · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 hx4
      refine ⟨-a, Set.mem_insert_of_mem _ (Or.inl ⟨a, ha, rfl⟩), ?_⟩
      have : x - -a = x + a := by ring
      rw [this]
      exact Or.inl hxa

/-- The recorded `#S < 𝔠` case, re-derived from the covering reduction: a set of size `< 𝔠`
cannot cover `ℝ` with `< 𝔠` translates. -/
theorem witness_of_mk_lt_continuum' (hlt : #S < 𝔠) : Witness S := by
  refine witness_of_no_small_cover S fun T hT hcover => ?_
  have hYle : #(S ∪ ((fun x => 2 * x) ⁻¹' S) : Set ℝ) ≤ #S + #S := by
    refine le_trans (Cardinal.mk_union_le _ _) (add_le_add le_rfl ?_)
    rw [preimage_two_mul_eq_image]
    exact Cardinal.mk_image_le
  -- the covering map `x ↦ (t, x - t)` is injective into `T × Y`
  have hinj : #(univ : Set ℝ) ≤ #T * #(S ∪ ((fun x => 2 * x) ⁻¹' S) : Set ℝ) := by
    classical
    have hmap : ∀ x : ℝ, ∃ p : T × (S ∪ ((fun x => 2 * x) ⁻¹' S) : Set ℝ),
        x = (p.1 : ℝ) + (p.2 : ℝ) := by
      intro x
      obtain ⟨t, htT, hxt⟩ := hcover x
      exact ⟨(⟨t, htT⟩, ⟨x - t, hxt⟩), by ring⟩
    choose f hf using hmap
    have hfinj : Function.Injective f := by
      intro a b hab
      rw [hf a, hf b, hab]
    calc #(univ : Set ℝ) = #ℝ := Cardinal.mk_univ
      _ ≤ #(T × (S ∪ ((fun x => 2 * x) ⁻¹' S) : Set ℝ)) := Cardinal.mk_le_of_injective hfinj
      _ = #T * #(S ∪ ((fun x => 2 * x) ⁻¹' S) : Set ℝ) := by
          rw [Cardinal.mk_prod]; simp
  have hSS : #S + #S < 𝔠 := Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum hlt hlt
  have hYlt : #(S ∪ ((fun x => 2 * x) ⁻¹' S) : Set ℝ) < 𝔠 := hYle.trans_lt hSS
  have hprod : #T * #(S ∪ ((fun x => 2 * x) ⁻¹' S) : Set ℝ) < 𝔠 :=
    Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum hT hYlt
  have h𝔠 : (𝔠 : Cardinal) ≤ #(univ : Set ℝ) := by
    rw [Cardinal.mk_univ, Cardinal.mk_real]
  exact absurd ((h𝔠.trans hinj).trans_lt hprod) (lt_irrefl _)

/-- Sum-freeness pulls back along additive maps. -/
theorem sumFree_preimage {φ : ℝ →+ ℝ} (hSF : SumFree S) : SumFree (φ ⁻¹' S) := by
  intro a ha b hb hab
  refine hSF (φ a) ha (φ b) hb ?_
  have : φ a + φ b = φ (a + b) := (map_add φ a b).symm
  rw [this]
  exact hab

/-- **Transfer principle.** The conclusion of Erdős 949 pulls back along injective additive
maps: if it holds for `φ ⁻¹' S` then it holds for `S`. Hence one may replace `ℝ` by any
`ℚ`-subspace of dimension continuum. -/
theorem witness_of_preimage {φ : ℝ →+ ℝ} (hφ : Function.Injective φ)
    (h : Witness (φ ⁻¹' S)) : Witness S := by
  obtain ⟨A, hAS, hcard, hAA⟩ := h
  refine ⟨φ '' A, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hAS ha
  · rw [Cardinal.mk_image_eq hφ, hcard]
  · rw [Set.add_subset_iff]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hsum : φ a + φ b = φ (a + b) := (map_add φ a b).symm
    rw [hsum]
    exact hAA (Set.add_mem_add ha hb)

/-- Any continuum-sized additively closed set avoiding `S` settles 949 for `S`.
(For instance a continuum-sized subgroup of `ℝ` disjoint from `S`.) -/
theorem witness_of_addClosed {B : Set ℝ} (hB : B ⊆ Sᶜ) (hcard : #B = 𝔠) (hadd : B + B ⊆ B) :
    Witness S :=
  ⟨B, hB, hcard, fun _ hx => hB (hadd hx)⟩

end Erdos949Close

/-! ### Axiom receipts -/

#print axioms Erdos949Close.witness_of_no_small_cover
#print axioms Erdos949Close.witness_of_mk_lt_continuum'
#print axioms Erdos949Close.sumFree_preimage
#print axioms Erdos949Close.witness_of_preimage
#print axioms Erdos949Close.witness_of_addClosed
