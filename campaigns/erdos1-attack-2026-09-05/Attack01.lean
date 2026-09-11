import Mathlib

/-!
# Erdős Problem #1 — distinct subset sums (Erdős–Moser).  ATTACK 01.

*Reference:* [erdosproblems.com/1](https://www.erdosproblems.com/1).  Prize $500. OPEN.

**The open problem.**  If `A ⊆ {1,…,N}` with `|A| = n` has all `2^n` subset sums distinct,
must `N ≫ 2^n`?  Formally (DeepMind `formal-conjectures`, `ErdosProblems/1.lean`):

    ∃ C > 0, ∀ N A, IsSumDistinctSet A N → N ≠ 0 → C * 2 ^ A.card < N

That statement is **NOT attacked here as a close** and is **NOT weakened**.  What this file does
is discharge finite/decidable obligations that the corpus left as `sorry`, and extract from an
explicit witness a *two-sided* fact about the conjectured constant.

**Obligations.**

| # | obligation | disposition |
|---|---|---|
| O0 | control: reproduce the corpus' proved `variants.weaker` verbatim | compile sanity |
| O1 | bridge: subtype-injectivity ⟺ `(powerset.image sum).card = powerset.card` | sealed |
| O2 | `variants.least_N_5` : min N for a 5-element sum-distinct set is 13 | **SEALED** (corpus `sorry`) |
| O3 | `least_N_4` : min N for a 4-element sum-distinct set is 7 (not in corpus) | **SEALED** (new) |
| O4 | Conway–Guy set at n = 9 is sum-distinct with max 161 | sealed |
| O5 | upper half of `variants.least_N_9` : `161 ∈ {N | …}` | sealed (half of a corpus `sorry`) |
| O6 | **obstruction**: every constant witnessing `erdos_1` is `< 161/512` | **SEALED** |

`native_decide` is forbidden; every finite check below is real kernel reduction via `decide`.
-/

namespace Erdos1Attack

open Finset

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## The specification, reproduced VERBATIM from `formal-conjectures/ErdosProblems/1.lean`. -/

/--
A finite set of naturals $A$ is said to be a sum-distinct set for $N \in \mathbb{N}$ if
$A\subseteq\{1, ..., N\}$ and the sums $\sum_{a\in S}a$ are distinct for all $S\subseteq A$
-/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

/-! ## O0 — CONTROL.  The corpus' own proved variant, reproduced verbatim.
Nothing below depends on it; it exists so that a green run of this file also certifies that the
ambient Mathlib still elaborates the corpus proof, i.e. that the spec has not drifted. -/

/-- The trivial lower bound is $N \gg 2^n / n$. -/
theorem control_weaker : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ)
    (_ : IsSumDistinctSet A N), N ≠ 0 → C * 2 ^ A.card / A.card < N := by
  refine ⟨1/3, by norm_num, fun N A ⟨hA1, hA2⟩ hN => ?_⟩
  have key : 2 ^ A.card ≤ A.card * N + 1 := by
    rw [← Finset.card_powerset]
    exact (Finset.card_le_card_of_injOn (Finset.sum · id)
      (fun S hS => Finset.mem_range.mpr <| Nat.lt_add_one_of_le <|
        (Finset.sum_le_card_nsmul S id N fun i hi =>
          (Finset.mem_Icc.mp (hA1 (Finset.mem_powerset.mp hS hi))).2).trans
          (Nat.mul_le_mul_right N (Finset.card_le_card (Finset.mem_powerset.mp hS))))
      (fun a ha b hb hab => by
        have := @hA2 ⟨a, ha⟩ ⟨b, hb⟩ hab; simp at this; exact this)).trans_eq
      (Finset.card_range _)
  rcases eq_or_ne A.card 0 with hc | hc
  · simp [hc]; positivity
  · rw [div_lt_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc))]
    nlinarith [show (2 : ℝ) ^ A.card ≤ ↑A.card * ↑N + 1 from by exact_mod_cast key,
      show (1 : ℝ) ≤ ↑A.card from by exact_mod_cast Nat.pos_of_ne_zero hc,
      show (1 : ℝ) ≤ (N : ℝ) from by exact_mod_cast Nat.pos_of_ne_zero hN]

/-! ## O1 — THE BRIDGE.

The spec phrases sum-distinctness as injectivity of a function on the *subtype* `↥A.powerset`,
which the kernel cannot evaluate.  These two lemmas move it to a `Finset` cardinality identity,
which the kernel *can* evaluate.  Both directions are needed: `←` to build witnesses, `→` to
exclude candidates in an exhaustion. -/

/-- `(A.powerset.image sum).card = A.powerset.card` ⟹ the spec's subtype injectivity. -/
theorem injective_of_card_image {A : Finset ℕ}
    (h : (A.powerset.image (fun S => S.sum id)).card = A.powerset.card) :
    (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective := by
  have hinj : Set.InjOn (fun S : Finset ℕ => S.sum id) ↑A.powerset :=
    Finset.injOn_of_card_image_eq h
  rintro ⟨S, hS⟩ ⟨T, hT⟩ hst
  exact Subtype.ext (hinj (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT) hst)

/-- The spec's subtype injectivity ⟹ `(A.powerset.image sum).card = A.powerset.card`. -/
theorem card_image_of_injective {A : Finset ℕ}
    (h : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
    (A.powerset.image (fun S => S.sum id)).card = A.powerset.card := by
  refine Finset.card_image_of_injOn (fun S hS T hT hst => ?_)
  exact congrArg Subtype.val (h (a₁ := ⟨S, Finset.mem_coe.mp hS⟩)
    (a₂ := ⟨T, Finset.mem_coe.mp hT⟩) hst)

/-- Convenience: a sum-distinct set of card `n` has exactly `2 ^ n` distinct subset sums. -/
theorem card_image_eq_two_pow {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) :
    (A.powerset.image (fun S => S.sum id)).card = 2 ^ A.card := by
  rw [card_image_of_injective h.2, Finset.card_powerset]

/-! ## O3 — `least_N_4 = 7`.  Not present in the corpus.  Witness `{3,5,6,7}`; exhaustion over
the 15 four-element subsets of `[1,6]`. -/

theorem exhaustion_6_4 :
    ((Finset.Icc 1 6).powerset.filter
      (fun A => A.card = 4 ∧ (A.powerset.image (fun S => S.sum id)).card = 16)) = ∅ := by
  decide

theorem least_N_4 : IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 4 } 7 := by
  constructor
  · refine ⟨{3, 5, 6, 7}, ⟨?_, injective_of_card_image ?_⟩, by decide⟩
    · decide
    · decide
  · rintro N ⟨A, ⟨hsub, hinj⟩, hcard⟩
    by_contra hlt
    push_neg at hlt
    have hA6 : A ∈ (Finset.Icc 1 6).powerset :=
      Finset.mem_powerset.mpr (hsub.trans (Finset.Icc_subset_Icc_right (by omega)))
    have himg : (A.powerset.image (fun S => S.sum id)).card = 16 := by
      rw [card_image_of_injective hinj, Finset.card_powerset, hcard]
    have hmem : A ∈ ((Finset.Icc 1 6).powerset.filter
        (fun A => A.card = 4 ∧ (A.powerset.image (fun S => S.sum id)).card = 16)) :=
      Finset.mem_filter.mpr ⟨hA6, hcard, himg⟩
    rw [exhaustion_6_4] at hmem
    exact absurd hmem (Finset.not_mem_empty A)

/-! ## O2 — `variants.least_N_5 = 13`.  This is a `sorry` in the corpus, categorised
`research solved` (OEIS A276661).  Witness `{6,9,11,12,13}` (the Conway–Guy set at n = 5);
exhaustion over the 792 five-element subsets of `[1,12]`. -/

/-- **No** 5-element subset of `{1,…,12}` has 32 distinct subset sums.  Kernel-checked
exhaustion over the full 4096-element powerset of `Finset.Icc 1 12`. -/
theorem exhaustion_12_5 :
    ((Finset.Icc 1 12).powerset.filter
      (fun A => A.card = 5 ∧ (A.powerset.image (fun S => S.sum id)).card = 32)) = ∅ := by
  decide

/-- `{6,9,11,12,13}` is sum-distinct inside `{1,…,13}`. -/
theorem witness_5 : IsSumDistinctSet {6, 9, 11, 12, 13} 13 := by
  refine ⟨by decide, injective_of_card_image (by decide)⟩

/--
The minimal value of $N$ such that there exists a sum-distinct set with five
elements is $13$.   (https://oeis.org/A276661)

**Corpus status: `sorry`, category `research solved`.  SEALED HERE.**
-/
theorem least_N_5 : IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 5 } 13 := by
  constructor
  · exact ⟨{6, 9, 11, 12, 13}, witness_5, by decide⟩
  · rintro N ⟨A, ⟨hsub, hinj⟩, hcard⟩
    by_contra hlt
    push_neg at hlt
    have hA12 : A ∈ (Finset.Icc 1 12).powerset :=
      Finset.mem_powerset.mpr (hsub.trans (Finset.Icc_subset_Icc_right (by omega)))
    have himg : (A.powerset.image (fun S => S.sum id)).card = 32 := by
      rw [card_image_of_injective hinj, Finset.card_powerset, hcard]
    have hmem : A ∈ ((Finset.Icc 1 12).powerset.filter
        (fun A => A.card = 5 ∧ (A.powerset.image (fun S => S.sum id)).card = 32)) :=
      Finset.mem_filter.mpr ⟨hA12, hcard, himg⟩
    rw [exhaustion_12_5] at hmem
    exact absurd hmem (Finset.not_mem_empty A)

/-! ## O4/O5/O6 — the Conway–Guy witness at n = 9, and what it forces on the constant. -/

/-- The Conway–Guy set at `n = 9`: `{u₉ - u₉₋ᵢ}` for the sequence
`u = 0,1,2,4,7,13,24,44,84,161` (OEIS A005318).  Largest element `161`. -/
def CG9 : Finset ℕ := {77, 117, 137, 148, 154, 157, 159, 160, 161}

theorem CG9_card : CG9.card = 9 := by decide

theorem CG9_subset : CG9 ⊆ Finset.Icc 1 161 := by
  intro x hx
  simp only [CG9, Finset.mem_insert, Finset.mem_singleton] at hx
  rw [Finset.mem_Icc]
  omega

/-- **O4.**  `CG9` is sum-distinct: all `2^9 = 512` of its subset sums are distinct.
Kernel-checked. -/
theorem CG9_sumDistinct : IsSumDistinctSet CG9 161 :=
  ⟨CG9_subset, injective_of_card_image (by decide)⟩

/-- **O5.**  The upper half of the corpus' `variants.least_N_9` (`sorry`, `research solved`):
`161` really is attained by a 9-element sum-distinct set.  The *lower* half — that no
9-element sum-distinct set fits inside `{1,…,160}` — is NOT proved here; see TERMINAL.json. -/
theorem least_N_9_mem : (161 : ℕ) ∈ { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 9 } :=
  ⟨CG9, CG9_sumDistinct, CG9_card⟩

/--
**O6 — THE OBSTRUCTION.**  Every constant that witnesses Erdős #1 is strictly below `161/512`.

The corpus statement of the open problem is `∃ C > 0, ∀ N A, IsSumDistinctSet A N → N ≠ 0 →
C * 2 ^ A.card < N`.  The Conway–Guy set at `n = 9` sits inside `{1,…,161}`, so any such `C`
obeys `C * 2^9 < 161`, i.e. `C < 161/512 = 0.314453125…`.

This does not resolve the problem in either direction.  It is a **typed obstruction**: it rules
out, unconditionally and by kernel, every proof of `erdos_1` that would supply a constant
`C ≥ 161/512`.
-/
theorem erdos1_constant_lt_161_512 :
    ∀ C : ℝ, (∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
      N ≠ 0 → C * 2 ^ A.card < N) → C < 161 / 512 := by
  intro C h
  have hc := h 161 CG9 CG9_sumDistinct (by norm_num)
  rw [CG9_card] at hc
  norm_num at hc
  linarith

/-- Restated against the corpus' exact existential shape. -/
theorem erdos1_no_constant_ge_161_512 :
    ¬ ∃ C : ℝ, 161 / 512 ≤ C ∧ ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
      N ≠ 0 → C * 2 ^ A.card < N := by
  rintro ⟨C, hge, h⟩
  exact absurd (erdos1_constant_lt_161_512 C h) (not_lt.mpr hge)

end Erdos1Attack

#print axioms Erdos1Attack.control_weaker
#print axioms Erdos1Attack.injective_of_card_image
#print axioms Erdos1Attack.card_image_of_injective
#print axioms Erdos1Attack.card_image_eq_two_pow
#print axioms Erdos1Attack.exhaustion_6_4
#print axioms Erdos1Attack.least_N_4
#print axioms Erdos1Attack.exhaustion_12_5
#print axioms Erdos1Attack.witness_5
#print axioms Erdos1Attack.least_N_5
#print axioms Erdos1Attack.CG9_card
#print axioms Erdos1Attack.CG9_subset
#print axioms Erdos1Attack.CG9_sumDistinct
#print axioms Erdos1Attack.least_N_9_mem
#print axioms Erdos1Attack.erdos1_constant_lt_161_512
#print axioms Erdos1Attack.erdos1_no_constant_ge_161_512
