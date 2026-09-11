import Mathlib

/-!
# Erdős 949 — the regularity encirclement (campaign erdos949-close-2026-09-05)

Problem (erdosproblems.com/949, open): let `S ⊆ ℝ` contain no solution of `a + b = c`
(sum-free, diagonal included). Must there be `A ⊆ ℝ \ S` of cardinality continuum with
`A + A ⊆ ℝ \ S`?

Recorded on the problem page: the Sidon variant (AlphaProof), the case `#S < 𝔠`
(Dillies' Zorn argument), and the case where `S` has the Baire property.

This file banks, kernel-checked and sorry-free:

* `sumFree_disjoint_sub` : a sum-free set is disjoint from its own difference set.
  (`S ∩ (S - S) = ∅`.)  This is the lever for everything below.
* `witness_of_gap`       : if `S` misses a symmetric interval around `0`, that interval halved
  is a witness. So the problem is only about sets accumulating at `0`.
* `witness_of_measurable_pos` : **the measure-side analogue of the recorded Baire-property
  result**: a sum-free *measurable* `S` of positive measure satisfies the conclusion.
  Proof: Steinhaus (`S - S` is a neighbourhood of `0`) + the lever + the interval witness.
  In particular a measurable sum-free set of positive measure is bounded away from `0`.
* `exists_maximal_partial` : the Zorn core, in covering form (no sum-freeness needed).
* `witness_of_mk_lt_continuum` : re-derivation of the recorded `#S < 𝔠` case from the core.
* `uncountable_witness_of_volume_zero` : **new**, ZFC: for *any* null `S` (sum-free or not)
  there is an UNCOUNTABLE `A ⊆ Sᶜ` with `A + A ⊆ Sᶜ`.  (Under CH this closes the null case;
  in ZFC the null case needs Mycielski's theorem, which Mathlib does not have — see
  CLAIMS.md, where that argument is recorded as a paper proof, NOT kernel-checked.)
* `witness_of_fourfold` : the whole problem is a statement about FOUR-fold sums — if some
  `t ∈ S` has `S + S + 2t` disjoint from `S`, then `S + t` is already a witness.
* `measurable_dichotomy` : measurable `S` ⇒ witness, or (null case) uncountable partial witness.

Non-vacuity controls at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Cardinal MeasureTheory
open scoped Pointwise Cardinal Topology

namespace Erdos949Close

variable {S : Set ℝ}

/-- `S` contains no solution of `a + b = c` (the diagonal `a = b` is included). -/
def SumFree (S : Set ℝ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S

/-- The conclusion asked for by Erdős 949. -/
def Witness (S : Set ℝ) : Prop := ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ

/-! ### The lever -/

/-- A sum-free set is disjoint from its own difference set. -/
theorem sumFree_disjoint_sub (hS : SumFree S) : Disjoint S (S - S) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.1 hx'
  have hxb : x + b = a := by rw [← hab]; ring
  exact hS x hx b hb (hxb ▸ ha)

/-- Restatement: `S - S` lies in the complement of `S`. -/
theorem sub_subset_compl (hS : SumFree S) : S - S ⊆ Sᶜ := fun _ hx =>
  Set.disjoint_right.1 (sumFree_disjoint_sub hS) hx

/-! ### The interval witness -/

/-- If `S` misses the symmetric interval `(-ε, ε)`, then `(-ε/2, ε/2)` is a witness. -/
theorem witness_of_gap {ε : ℝ} (hε : 0 < ε) (h : Ioo (-ε) ε ⊆ Sᶜ) : Witness S := by
  refine ⟨Ioo (-(ε / 2)) (ε / 2), fun x hx => h (Set.mem_Ioo.2 ⟨by linarith [hx.1], by
    linarith [hx.2]⟩), Cardinal.mk_Ioo_real (by linarith), ?_⟩
  rw [Set.add_subset_iff]
  intro x hx y hy
  exact h (Set.mem_Ioo.2 ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩)

/-! ### The measure side: Steinhaus -/

/-- **Measure-side analogue of the recorded Baire-property partial result.**
A measurable sum-free set of positive measure satisfies the conclusion of Erdős 949. -/
theorem witness_of_measurable_pos (hSF : SumFree S) (hm : MeasurableSet S)
    (hpos : 0 < volume S) : Witness S := by
  have hst : S - S ∈ 𝓝 (0 : ℝ) :=
    MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume S hm hpos
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hst
  refine witness_of_gap hε (fun x hx => ?_)
  have hxb : x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Real.ball_eq_Ioo]
    simpa using hx
  exact sub_subset_compl hSF (hball hxb)

/-- A measurable sum-free set of positive measure is bounded away from the origin. -/
theorem gap_of_measurable_pos (hSF : SumFree S) (hm : MeasurableSet S) (hpos : 0 < volume S) :
    ∃ ε > 0, Ioo (-ε) ε ⊆ Sᶜ := by
  have hst : S - S ∈ 𝓝 (0 : ℝ) :=
    MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume S hm hpos
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hst
  refine ⟨ε, hε, fun x hx => ?_⟩
  have hxb : x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Real.ball_eq_Ioo]
    simpa using hx
  exact sub_subset_compl hSF (hball hxb)

/-! ### The Zorn core, in covering form -/

/-- Zorn core (no sum-freeness needed): a maximal partial witness `A` exists, and maximality
says exactly that every `x` outside `S`, outside `S/2` and outside `A` is blocked by some
`a ∈ A` with `x + a ∈ S`. Equivalently `ℝ` is covered by `S`, `S/2`, `A` and the `#A`
translates `S - a`. -/
theorem exists_maximal_partial (S : Set ℝ) :
    ∃ A : Set ℝ, A ⊆ Sᶜ ∧ (∀ x ∈ A, ∀ y ∈ A, x + y ∉ S) ∧
      ∀ x : ℝ, x ∉ S → 2 * x ∉ S → x ∉ A → ∃ a ∈ A, x + a ∈ S := by
  classical
  set P : Set (Set ℝ) := {A : Set ℝ | A ⊆ Sᶜ ∧ ∀ x ∈ A, ∀ y ∈ A, x + y ∉ S} with hP
  have hub : ∀ C ⊆ P, IsChain (· ⊆ ·) C → ∃ ub ∈ P, ∀ s ∈ C, s ⊆ ub := by
    intro C hC hchain
    refine ⟨⋃₀ C, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro x ⟨B, hB, hxB⟩
      exact (hC hB).1 hxB
    · rintro x ⟨B, hB, hxB⟩ y ⟨D, hD, hyD⟩
      obtain ⟨E, hE, hBE, hDE⟩ := hchain.directedOn _ hB _ hD
      exact (hC hE).2 x (hBE hxB) y (hDE hyD)
  obtain ⟨A, hA⟩ := zorn_subset P hub
  obtain ⟨hAS, hAA⟩ := hA.1
  refine ⟨A, hAS, hAA, ?_⟩
  intro x hxS h2x hxA
  by_contra hcon
  push_neg at hcon
  have hmem : insert x A ∈ P := by
    refine ⟨Set.insert_subset_iff.2 ⟨hxS, hAS⟩, ?_⟩
    rintro u (rfl | hu) v (rfl | hv)
    · simpa [two_mul] using h2x
    · exact hcon v hv
    · rw [add_comm]; exact hcon u hu
    · exact hAA u hu v hv
  exact hxA (hA.2 hmem (Set.subset_insert _ _) (Set.mem_insert _ _))

/-- The covering produced by a maximal partial witness, written with preimages. -/
theorem cover_of_maximal {A : Set ℝ}
    (hcov : ∀ x : ℝ, x ∉ S → 2 * x ∉ S → x ∉ A → ∃ a ∈ A, x + a ∈ S) :
    (univ : Set ℝ) ⊆ S ∪ ((fun x => 2 * x) ⁻¹' S) ∪ A ∪ ⋃ a ∈ A, ((fun x => x + a) ⁻¹' S) := by
  intro x _
  by_cases hxS : x ∈ S
  · exact Or.inl (Or.inl (Or.inl hxS))
  by_cases h2 : 2 * x ∈ S
  · exact Or.inl (Or.inl (Or.inr h2))
  by_cases hxA : x ∈ A
  · exact Or.inl (Or.inr hxA)
  · obtain ⟨a, ha, hxa⟩ := hcov x hxS h2 hxA
    exact Or.inr (Set.mem_biUnion ha hxa)

/-- A translate-preimage is a translate-image (used for the cardinality bookkeeping). -/
theorem preimage_add_eq_image (S : Set ℝ) (a : ℝ) :
    (fun x => x + a) ⁻¹' S = (fun s => s - a) '' S := by
  ext x
  constructor
  · intro hx; exact ⟨x + a, hx, by ring⟩
  · rintro ⟨s, hs, rfl⟩; simpa using hs

/-- The halving preimage is a halving image. -/
theorem preimage_two_mul_eq_image (S : Set ℝ) :
    (fun x => 2 * x) ⁻¹' S = (fun s => s / 2) '' S := by
  ext x
  constructor
  · intro hx; exact ⟨2 * x, hx, by ring⟩
  · rintro ⟨s, hs, rfl⟩; simpa [mul_div_cancel₀] using hs

/-! ### Corollary 1 (re-derivation of the recorded `#S < 𝔠` case) -/

theorem witness_of_mk_lt_continuum (hlt : #S < 𝔠) : Witness S := by
  obtain ⟨A, hAS, hAA, hcov⟩ := exists_maximal_partial S
  refine ⟨A, hAS, ?_, Set.add_subset_iff.2 hAA⟩
  by_contra hne
  have hAle : #A ≤ 𝔠 := (Cardinal.mk_set_le A).trans_eq Cardinal.mk_real
  have hA𝔠 : #A < 𝔠 := lt_of_le_of_ne hAle hne
  have hcover := cover_of_maximal (S := S) hcov
  have h2 : #((fun x => 2 * x) ⁻¹' S : Set ℝ) ≤ #S := by
    rw [preimage_two_mul_eq_image]
    exact Cardinal.mk_image_le
  have hU : #(⋃ a ∈ A, ((fun x => x + a) ⁻¹' S) : Set ℝ) ≤ #A * #S := by
    rcases A.eq_empty_or_nonempty with rfl | hAne
    · simp
    · have : Nonempty A := hAne.to_subtype
      refine le_trans (Cardinal.mk_biUnion_le _ _) ?_
      refine mul_le_mul_left' (ciSup_le fun a => ?_) _
      rw [preimage_add_eq_image]
      exact Cardinal.mk_image_le
  have hchain :
      (𝔠 : Cardinal) ≤ #S + #S + #A + #A * #S := by
    calc (𝔠 : Cardinal) = #(univ : Set ℝ) := by rw [Cardinal.mk_univ, Cardinal.mk_real]
      _ ≤ #(S ∪ ((fun x => 2 * x) ⁻¹' S) ∪ A ∪ ⋃ a ∈ A, ((fun x => x + a) ⁻¹' S) : Set ℝ) :=
          Cardinal.mk_le_mk_of_subset hcover
      _ ≤ #(S ∪ ((fun x => 2 * x) ⁻¹' S) ∪ A : Set ℝ) +
            #(⋃ a ∈ A, ((fun x => x + a) ⁻¹' S) : Set ℝ) := Cardinal.mk_union_le _ _
      _ ≤ (#(S ∪ ((fun x => 2 * x) ⁻¹' S) : Set ℝ) + #A) +
            #(⋃ a ∈ A, ((fun x => x + a) ⁻¹' S) : Set ℝ) :=
          add_le_add (Cardinal.mk_union_le _ _) le_rfl
      _ ≤ ((#S + #((fun x => 2 * x) ⁻¹' S : Set ℝ)) + #A) +
            #(⋃ a ∈ A, ((fun x => x + a) ⁻¹' S) : Set ℝ) :=
          add_le_add (add_le_add (Cardinal.mk_union_le _ _) le_rfl) le_rfl
      _ ≤ #S + #S + #A + #A * #S :=
          add_le_add (add_le_add (add_le_add le_rfl h2) le_rfl) hU
  have hlt' : #S + #S + #A + #A * #S < 𝔠 := by
    have h1 : #S + #S < 𝔠 := Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum hlt hlt
    have h2' : #S + #S + #A < 𝔠 := Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum h1 hA𝔠
    have h3 : #A * #S < 𝔠 := Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum hA𝔠 hlt
    exact Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum h2' h3
  exact absurd (hchain.trans_lt hlt') (lt_irrefl _)

/-! ### Corollary 2 (NEW): null sets admit an uncountable partial witness -/

/-- For any Lebesgue-null `S ⊆ ℝ` (sum-freeness not needed) there is an **uncountable**
`A ⊆ Sᶜ` with `A + A ⊆ Sᶜ`. -/
theorem uncountable_witness_of_volume_zero (hvol : volume S = 0) :
    ∃ A : Set ℝ, A ⊆ Sᶜ ∧ A + A ⊆ Sᶜ ∧ ℵ₀ < #A := by
  obtain ⟨A, hAS, hAA, hcov⟩ := exists_maximal_partial S
  refine ⟨A, hAS, Set.add_subset_iff.2 hAA, ?_⟩
  by_contra hle
  push_neg at hle
  have hcount : A.Countable := Set.countable_coe_iff.1 (Cardinal.mk_le_aleph0_iff.1 hle)
  have h2 : volume ((fun x => 2 * x) ⁻¹' S) = 0 := by
    rw [Real.volume_preimage_mul_left (by norm_num), hvol, mul_zero]
  have hA0 : volume A = 0 := hcount.measure_zero volume
  have hU : volume (⋃ a ∈ A, ((fun x => x + a) ⁻¹' S)) = 0 := by
    refine (measure_biUnion_null_iff hcount).2 fun a _ => ?_
    rw [MeasureTheory.measure_preimage_add_right volume a S, hvol]
  have hcover := cover_of_maximal (S := S) hcov
  have : volume (univ : Set ℝ) = 0 := by
    refine le_antisymm ?_ _root_.zero_le
    calc volume (univ : Set ℝ)
        ≤ volume (S ∪ ((fun x => 2 * x) ⁻¹' S) ∪ A ∪ ⋃ a ∈ A, ((fun x => x + a) ⁻¹' S)) :=
          measure_mono hcover
      _ ≤ volume (S ∪ ((fun x => 2 * x) ⁻¹' S) ∪ A) +
            volume (⋃ a ∈ A, ((fun x => x + a) ⁻¹' S)) := measure_union_le _ _
      _ ≤ (volume (S ∪ ((fun x => 2 * x) ⁻¹' S)) + volume A) +
            volume (⋃ a ∈ A, ((fun x => x + a) ⁻¹' S)) :=
          add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ((volume S + volume ((fun x => 2 * x) ⁻¹' S)) + volume A) +
            volume (⋃ a ∈ A, ((fun x => x + a) ⁻¹' S)) :=
          add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
      _ = 0 := by rw [hvol, h2, hA0, hU]; simp
  rw [Real.volume_univ] at this
  exact ENNReal.top_ne_zero this

/-! ### Corollary 3: the four-fold reduction -/

/-- Sum-freeness makes `S + t` automatically disjoint from `S` for `t ∈ S`. So the entire
content of Erdős 949 is a statement about FOUR-fold sums: if some `t ∈ S` has
`S + S + 2t` disjoint from `S`, the translate `S + t` is already a witness. -/
theorem witness_of_fourfold (hSF : SumFree S) (h𝔠 : #S = 𝔠) {t : ℝ} (ht : t ∈ S)
    (h4 : ∀ a ∈ S, ∀ b ∈ S, a + b + 2 * t ∉ S) : Witness S := by
  refine ⟨(fun s => s + t) '' S, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hSF s hs t ht
  · rw [Cardinal.mk_image_eq (add_left_injective t), h𝔠]
  · rw [Set.add_subset_iff]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have : a + t + (b + t) = a + b + 2 * t := by ring
    rw [this]
    exact h4 a ha b hb

/-! ### The measurable dichotomy -/

/-- For measurable sum-free `S`: either the full conclusion holds (positive measure), or
`S` is null and we still get an uncountable partial witness. -/
theorem measurable_dichotomy (hSF : SumFree S) (hm : MeasurableSet S) :
    Witness S ∨ (∃ A : Set ℝ, A ⊆ Sᶜ ∧ A + A ⊆ Sᶜ ∧ ℵ₀ < #A) := by
  by_cases h : volume S = 0
  · exact Or.inr (uncountable_witness_of_volume_zero h)
  · exact Or.inl (witness_of_measurable_pos hSF hm (pos_iff_ne_zero.2 h))

/-! ### Non-vacuity controls -/

/-- Control: `[1, 2)` is sum-free, measurable and of positive measure, so
`witness_of_measurable_pos` is not vacuous. -/
theorem control_Ico_sumFree : SumFree (Ico (1 : ℝ) 2) := by
  rintro a ⟨ha1, ha2⟩ b ⟨hb1, hb2⟩ ⟨hab1, hab2⟩
  linarith

theorem control_Ico_witness : Witness (Ico (1 : ℝ) 2) := by
  refine witness_of_measurable_pos control_Ico_sumFree measurableSet_Ico ?_
  rw [Real.volume_Ico]
  norm_num

/-- Control: `Witness` is not a vacuously true predicate — it FAILS for `S = univ`
(there the complement is empty). So the statements above are not trivially satisfiable. -/
theorem control_witness_not_trivial : ¬ Witness (univ : Set ℝ) := by
  rintro ⟨A, hA, hcard, -⟩
  have hAe : A = ∅ := by simpa using hA
  rw [hAe] at hcard
  have h0 : (0 : Cardinal) = 𝔠 := by simpa using hcard
  have hle : (ℵ₀ : Cardinal) ≤ 0 := by rw [h0]; exact Cardinal.aleph0_le_continuum
  exact Cardinal.aleph0_ne_zero (le_antisymm hle _root_.zero_le)

end Erdos949Close

/-! ### Axiom receipts -/

#print axioms Erdos949Close.sumFree_disjoint_sub
#print axioms Erdos949Close.sub_subset_compl
#print axioms Erdos949Close.witness_of_gap
#print axioms Erdos949Close.witness_of_measurable_pos
#print axioms Erdos949Close.gap_of_measurable_pos
#print axioms Erdos949Close.exists_maximal_partial
#print axioms Erdos949Close.cover_of_maximal
#print axioms Erdos949Close.witness_of_mk_lt_continuum
#print axioms Erdos949Close.uncountable_witness_of_volume_zero
#print axioms Erdos949Close.witness_of_fourfold
#print axioms Erdos949Close.measurable_dichotomy
#print axioms Erdos949Close.control_Ico_sumFree
#print axioms Erdos949Close.control_Ico_witness
#print axioms Erdos949Close.control_witness_not_trivial
