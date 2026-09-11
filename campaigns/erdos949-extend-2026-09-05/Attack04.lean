import Mathlib

/-!
Erdős 949 — **the actual statement, small-cardinality half** (campaign erdos949-extend, 2026-09-05).

## Why this is a NEW angle (Attack01–03 did not die, they finished, and they missed the target)

Attack01–03 all sealed clean (`decide +kernel` finite core, monoid generalisation, sharpness,
multiplier minimality, the k-fold Hindman theorem).  But NONE of them touches Erdős 949's own
question, which asks for a set of cardinality **continuum**:

  *Let `S ⊆ ℝ` contain no solution to `a + b = c`.  Must there be `A ⊆ ℝ \ S` with `#A = 𝔠` and
  `A + A ⊆ ℝ \ S`?*

  * Attack01 / Attack03 prove statements about `q ∈ {1,…,5}` — a finite side-problem.
  * Attack02's `erdos949_hindman_kfold` produces an infinite `A`, but a **countable** one
    (`A = Set.range f` for an injective `f : ℕ → ℕ`).  `#A = ℵ₀ < 𝔠`.

So the previous angle is exhausted at `ℵ₀` and cannot be pushed to `𝔠` by more Hindman: Hindman's
theorem is a statement about `ℕ` and returns a countable stream.  Reaching `𝔠` needs a
cardinality argument, not a Ramsey argument.  That is this file.

## What is proved here

`erdos949_small_cardinality` — for EVERY `S ⊆ ℝ` with `#S < 𝔠` (no sum-free hypothesis at all)
there is `A ⊆ Sᶜ` with `#A = 𝔠` and `A + A ⊆ Sᶜ`.  Zorn gives a maximal such `A`; maximality
forces `Sᶜ ∩ (S/2)ᶜ ⊆ A ∪ ⋃_{a ∈ A} (S - a)`, and the left side has size `𝔠`, so `#A = 𝔠`.

`erdos949_holds_for_small_sumfree` — Erdős 949's conclusion therefore holds for every sum-free
`S` of size `< 𝔠`.

`erdos949_reduces_to_continuum` — **the payoff.**  Erdős 949 is now EQUIVALENT to its own
`#S = 𝔠` special case.  The whole problem is confined to sets of full cardinality.

`erdos949_conclusion_control` — known-answer control: the conclusion is false for `S = univ`, so
none of the above is vacuous.

## Honest boundary

This does NOT close Erdős 949.  The `#S = 𝔠` case (which is where the difficulty lives, and where
the repo's `erdos_949.variants.sidon` needed the Sidon property to make progress) remains open.
The argument below is a de-Sidonisation of the first branch of
`oracle/math/EG411Formal/FormalConjectures/ErdosProblems/949.lean`: that branch never used
`IsSidon`, a fact this file makes explicit and kernel-checks by removing the hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Cardinal
open scoped Cardinal Pointwise

namespace Erdos949Continuum

/-- **Erdős 949 for every set of cardinality less than the continuum.**
If `#S < 𝔠` then there is `A ⊆ Sᶜ` with `#A = 𝔠` and `A + A ⊆ Sᶜ`.  Note there is NO sum-free
hypothesis: the conclusion holds for an arbitrary small set. -/
theorem erdos949_small_cardinality (S : Set ℝ) (hS𝔠 : #S < 𝔠) :
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  simp only [Set.add_subset_iff]
  -- Zorn: a maximal `A ⊆ Sᶜ` with all pairwise sums outside `S`.
  obtain ⟨A, ⟨hAS, hAAS⟩, hAmax⟩ := by
    refine zorn_subset {A ⊆ Sᶜ | ∀ x ∈ A, ∀ y ∈ A, x + y ∉ S} ?_
    simp only [Set.setOf_and, Set.subset_inter_iff, Set.mem_inter_iff, Set.mem_setOf_eq, and_imp,
      and_assoc]
    refine fun C hCS hSC hC ↦ ⟨_, Set.iUnion₂_subset hCS, ?_, Set.subset_iUnion₂⟩
    simp only [Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
    rintro x A hA hx y B hB hy
    obtain ⟨D, hD, hAD, hBD⟩ := hC.directedOn _ hA _ hB
    exact hSC hD _ (hAD hx) _ (hBD hy)
  refine ⟨A, hAS, ?_, hAAS⟩
  -- By maximality, `Sᶜ ∩ (S / 2)ᶜ ⊆ A ∪ ⋃ a ∈ A, (S - a)`.
  replace hAmax : Sᶜ ∩ ((· / 2) '' S)ᶜ ⊆ A ∪ ⋃ a ∈ A, (· - a) '' S := by
    simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_image, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_eq_iff_mul_eq, mul_two, exists_eq_right',
      Set.mem_union, Set.mem_iUnion, sub_eq_iff_eq_add, exists_eq_right, exists_prop,
      or_iff_not_imp_left, and_imp]
    rintro x hxS hxxS hxA
    by_contra! hxAS
    refine hxA <| hAmax ?_ (Set.subset_insert ..) (Set.mem_insert ..)
    simpa [Set.insert_subset_iff, forall_and, add_comm _ x, *] using ⟨hxAS, hAAS⟩
  -- `#(Sᶜ ∩ (S / 2)ᶜ) = 𝔠`, because `S` (and its halving image) are small.
  have hS𝔠' : #↑(Sᶜ ∩ ((· / 2) '' S)ᶜ) = 𝔠 := by
    rw [← Set.compl_union, mk_compl_of_infinite, mk_real]
    grw [mk_union_le, Cardinal.mk_real]
    refine add_lt_of_lt aleph0_le_continuum hS𝔠 ?_
    grw [mk_image_le]
    exact hS𝔠
  -- If `#A < 𝔠` then `𝔠 ≤ #A + #A * #S < 𝔠`, contradiction.
  refine (mk_real ▸ mk_set_le _).eq_of_not_lt fun hA𝔠 ↦ lt_irrefl 𝔠 ?_
  calc
    𝔠 = #↑(Sᶜ ∩ ((· / 2) '' S)ᶜ) := by rw [hS𝔠']
    _ ≤ #↑(A ∪ ⋃ a ∈ A, (· - a) '' S) := mk_subtype_mono hAmax
    _ ≤ #A + #A * #S := by
        obtain rfl | hA := A.eq_empty_or_nonempty
        · simp
        have : Nonempty A := hA.coe_sort
        grw [mk_union_le, mk_biUnion_le, ciSup_le fun _ ↦ mk_image_le]
    _ < 𝔠 := add_lt_of_lt aleph0_le_continuum hA𝔠 <| mul_lt_of_lt aleph0_le_continuum hA𝔠 hS𝔠

/-- **Erdős 949 holds for every sum-free set of cardinality less than the continuum.** -/
theorem erdos949_holds_for_small_sumfree (S : Set ℝ)
    (_hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) (hS𝔠 : #S < 𝔠) :
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ :=
  erdos949_small_cardinality S hS𝔠

/-- **THE REDUCTION.**  Erdős 949 is equivalent to its own `#S = 𝔠` special case: every sum-free
set of smaller cardinality is already handled by `erdos949_small_cardinality`. -/
theorem erdos949_reduces_to_continuum :
    (∀ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ) ↔
      (∀ S : Set ℝ, #S = 𝔠 → (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) →
        ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ) := by
  constructor
  · intro h S _ hS
    exact h S hS
  · intro h S hS
    obtain hlt | heq : #S < 𝔠 ∨ #S = 𝔠 := lt_or_eq_of_le <| by simpa using mk_set_le S
    · exact erdos949_small_cardinality S hlt
    · exact h S heq hS

/-- Known-answer control: the 949 conclusion FAILS for `S = univ` (whose complement is empty), so
the theorems above are not vacuous and the conclusion is a genuine constraint. -/
theorem erdos949_conclusion_control :
    ¬ ∃ A ⊆ (Set.univ : Set ℝ)ᶜ, #A = 𝔠 ∧ A + A ⊆ (Set.univ : Set ℝ)ᶜ := by
  rintro ⟨A, hA, hcard, -⟩
  rw [Set.compl_univ, Set.subset_empty_iff] at hA
  subst hA
  rw [Cardinal.mk_emptyCollection] at hcard
  exact absurd hcard.symm (ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos aleph0_le_continuum))

/-- Second control: `#S < 𝔠` is load-bearing in `erdos949_small_cardinality` — dropping it makes
the statement false, witnessed by `S = univ` (which has `#S = 𝔠`, not `< 𝔠`). -/
theorem erdos949_small_cardinality_hypothesis_needed :
    ¬ ∀ S : Set ℝ, ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  intro h
  exact erdos949_conclusion_control (h Set.univ)

end Erdos949Continuum

#print axioms Erdos949Continuum.erdos949_small_cardinality
#print axioms Erdos949Continuum.erdos949_holds_for_small_sumfree
#print axioms Erdos949Continuum.erdos949_reduces_to_continuum
#print axioms Erdos949Continuum.erdos949_conclusion_control
#print axioms Erdos949Continuum.erdos949_small_cardinality_hypothesis_needed
