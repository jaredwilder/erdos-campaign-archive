/-
Erdos Problem 1  (erdosproblems.com/1, $500) -- sum-distinct sets.

FROZEN SOURCE STATEMENT (google-deepmind/formal-conjectures, ErdosProblems/Erdos1.lean,
as held on this estate at
evidence/lean-source-intake/formal-conjectures-2026-07-18/candidates.json):

  If A subset {1,...,N} with |A| = n is such that the subset sums are distinct,
  then N >> 2^n.

`IsSumDistinctSet` below is transcribed byte-identically from that file.

PROVED HERE, sorry-free, Mathlib only:
  * `secondMoment`      the signed second-moment identity over the powerset
  * `sum_sq_lower`      a spread lower bound for any finset of distinct integers
  * `erdos1_sqrt`       2^(2n) <= 64 * n * N^2   i.e.  N >= 2^n / (8 * sqrt n)
  * `erdos1_sqrt_real`  the same in the real-valued shape of the frozen file
  * `witness6`,`witness7`  explicit sum-distinct sets of max 24 (n=6) and 44 (n=7)

NOT PROVED HERE: the target.  The target needs N >= C * 2^n with NO n-dependent
loss; `erdos1_sqrt` loses sqrt n.  The frozen file itself proves only
`erdos_1.variants.weaker`,  (1/3) * 2^n / n < N, the pigeonhole bound;
`erdos1_sqrt` is strictly stronger than that for n >= 8 (crossover receipted in receipts/compare.json).
-/

import Mathlib

namespace Erdos1

open Finset

/-- FROZEN. Byte-identical to formal-conjectures `Erdos1.IsSumDistinctSet`. -/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

/-- The same property, first-order and decidable. -/
def SumDistinct (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powerset, ∀ T ∈ A.powerset, S.sum id = T.sum id → S = T

theorem sumDistinct_iff (A : Finset ℕ) :
    SumDistinct A ↔ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective := by
  constructor
  · intro h a b hab
    obtain ⟨S, hS⟩ := a
    obtain ⟨T, hT⟩ := b
    exact Subtype.ext (h S hS T hT hab)
  · intro h S hS T hT hst
    exact congrArg Subtype.val (h (a₁ := ⟨S, hS⟩) (a₂ := ⟨T, hT⟩) hst)

/-- A finite, kernel-evaluable certificate for sum-distinctness. -/
theorem sumDistinct_of_card_image (A : Finset ℕ)
    (h : (A.powerset.image (fun S => S.sum id)).card = 2 ^ A.card) : SumDistinct A := by
  have h2 : (A.powerset.image (fun S => S.sum id)).card = A.powerset.card := by
    rw [h, Finset.card_powerset]
  have hinj := Finset.injOn_of_card_image_eq h2
  intro S hS T hT hst
  exact hinj (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT) hst

/-! ### The signed second-moment identity -/

/-- `∑_{S ⊆ A} (2·σ(S) − σ(A))² = 2^{|A|} · ∑_{a ∈ A} a²`: the ±1 cross terms cancel. -/
theorem secondMoment (A : Finset ℕ) :
    ∑ S ∈ A.powerset, (2 * ((S.sum id : ℕ) : ℤ) - ((A.sum id : ℕ) : ℤ)) ^ 2
      = 2 ^ A.card * ∑ a ∈ A, (a : ℤ) ^ 2 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a B ha ih =>
      have hsum : (((insert a B).sum id : ℕ) : ℤ) = (a : ℤ) + ((B.sum id : ℕ) : ℤ) := by
        rw [Finset.sum_insert ha]; simp only [id_eq]; push_cast; ring
      have h1 : ∑ S ∈ B.powerset, (2 * ((S.sum id : ℕ) : ℤ) - (((insert a B).sum id : ℕ) : ℤ)) ^ 2
              = ∑ S ∈ B.powerset,
                  ((2 * ((S.sum id : ℕ) : ℤ) - ((B.sum id : ℕ) : ℤ)) - (a : ℤ)) ^ 2 := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [hsum]; ring
      have h2 : ∑ S ∈ B.powerset,
                  (2 * (((insert a S).sum id : ℕ) : ℤ) - (((insert a B).sum id : ℕ) : ℤ)) ^ 2
              = ∑ S ∈ B.powerset,
                  ((2 * ((S.sum id : ℕ) : ℤ) - ((B.sum id : ℕ) : ℤ)) + (a : ℤ)) ^ 2 := by
        refine Finset.sum_congr rfl fun S hS => ?_
        have haS : a ∉ S := fun hmem => ha (Finset.mem_powerset.mp hS hmem)
        rw [hsum, Finset.sum_insert haS]
        simp only [id_eq]
        push_cast
        ring
      have h3 : ∑ S ∈ B.powerset,
                  (((2 * ((S.sum id : ℕ) : ℤ) - ((B.sum id : ℕ) : ℤ)) - (a : ℤ)) ^ 2
                   + ((2 * ((S.sum id : ℕ) : ℤ) - ((B.sum id : ℕ) : ℤ)) + (a : ℤ)) ^ 2)
              = ∑ S ∈ B.powerset,
                  (2 * (2 * ((S.sum id : ℕ) : ℤ) - ((B.sum id : ℕ) : ℤ)) ^ 2 + 2 * (a : ℤ) ^ 2) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        ring
      rw [Finset.sum_powerset_insert ha, h1, h2, ← Finset.sum_add_distrib, h3,
        Finset.sum_add_distrib, ← Finset.mul_sum, ih, Finset.sum_const,
        Finset.card_powerset, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
      push_cast
      ring

/-! ### The spread lower bound -/

/-- At most `2m+1` of a set of distinct integers lie in `[−m, m]`; every other one
contributes at least `(m+1)²` to the sum of squares. -/
theorem sum_sq_lower (T : Finset ℤ) (m : ℕ) :
    ((T.card : ℤ) - (2 * (m : ℤ) + 1)) * ((m : ℤ) + 1) ^ 2 ≤ ∑ x ∈ T, x ^ 2 := by
  classical
  set I : Finset ℤ := Finset.Icc (-(m : ℤ)) (m : ℤ) with hI
  have hIcard : (I.card : ℤ) = 2 * (m : ℤ) + 1 := by
    rw [hI, Int.card_Icc]
    omega
  set Tin : Finset ℤ := T.filter (fun x => x ∈ I) with hTin
  set Tout : Finset ℤ := T.filter (fun x => x ∉ I) with hTout
  have hsplit : Tin.card + Tout.card = T.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  have hin_le : (Tin.card : ℤ) ≤ (I.card : ℤ) := by
    have hs : Tin ⊆ I := fun x hx => (Finset.mem_filter.mp hx).2
    exact_mod_cast Finset.card_le_card hs
  have hout_ge : (T.card : ℤ) - (2 * (m : ℤ) + 1) ≤ (Tout.card : ℤ) := by
    have hc : (Tin.card : ℤ) + (Tout.card : ℤ) = (T.card : ℤ) := by exact_mod_cast hsplit
    rw [hIcard] at hin_le
    linarith
  have hbig : ∀ x ∈ Tout, ((m : ℤ) + 1) ^ 2 ≤ x ^ 2 := by
    intro x hx
    have hxI : x ∉ I := (Finset.mem_filter.mp hx).2
    rw [hI, Finset.mem_Icc] at hxI
    push_neg at hxI
    rcases lt_or_ge x (-(m : ℤ)) with hlt | hge
    · nlinarith [hlt]
    · have hgt : (m : ℤ) < x := hxI hge
      nlinarith [hgt]
  have hsum_out : ((Tout.card : ℤ)) * ((m : ℤ) + 1) ^ 2 ≤ ∑ x ∈ Tout, x ^ 2 := by
    calc ((Tout.card : ℤ)) * ((m : ℤ) + 1) ^ 2
        = ∑ _x ∈ Tout, ((m : ℤ) + 1) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ Tout, x ^ 2 := Finset.sum_le_sum hbig
  have hsub : ∑ x ∈ Tout, x ^ 2 ≤ ∑ x ∈ T, x ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro i _ _
    positivity
  have hpos : (0 : ℤ) ≤ ((m : ℤ) + 1) ^ 2 := by positivity
  nlinarith [hout_ge, hsum_out, hsub, hpos]

/-! ### The bound -/

theorem injOn_centred (A : Finset ℕ) (h : SumDistinct A) :
    Set.InjOn (fun S : Finset ℕ => 2 * ((S.sum id : ℕ) : ℤ) - ((A.sum id : ℕ) : ℤ))
      (A.powerset : Set (Finset ℕ)) := by
  intro S hS T hT hst
  simp only at hst
  exact h S (Finset.mem_coe.mp hS) T (Finset.mem_coe.mp hT) (by omega)

/-- **Main kernel-checked bound.**  A sum-distinct `A ⊆ [1,N]` with `|A| ≥ 2` obeys
`2^(2|A|) ≤ 64 · |A| · N²`, i.e. `N ≥ 2^|A| / (8 √|A|)`. -/
theorem erdos1_sqrt (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N)
    (hcard : 2 ≤ A.card) :
    2 ^ (2 * A.card) ≤ 64 * A.card * N ^ 2 := by
  classical
  obtain ⟨hAsub, hAinj⟩ := h
  have hSD : SumDistinct A := (sumDistinct_iff A).mpr hAinj
  set g : Finset ℕ → ℤ := fun S => 2 * ((S.sum id : ℕ) : ℤ) - ((A.sum id : ℕ) : ℤ) with hg
  set V : Finset ℤ := A.powerset.image g with hV
  have hinj := injOn_centred A hSD
  have hVcard : V.card = 2 ^ A.card := by
    rw [hV, Finset.card_image_of_injOn hinj, Finset.card_powerset]
  have hVsum : ∑ x ∈ V, x ^ 2 = ∑ S ∈ A.powerset, (g S) ^ 2 := by
    rw [hV]
    exact Finset.sum_image (fun S hS T hT hst =>
      hinj (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT) hst)
  have hmoment : ∑ S ∈ A.powerset, (g S) ^ 2 = 2 ^ A.card * ∑ a ∈ A, (a : ℤ) ^ 2 :=
    secondMoment A
  have hQ : ∑ a ∈ A, (a : ℤ) ^ 2 ≤ (A.card : ℤ) * (N : ℤ) ^ 2 := by
    calc ∑ a ∈ A, (a : ℤ) ^ 2 ≤ ∑ _a ∈ A, (N : ℤ) ^ 2 := by
          refine Finset.sum_le_sum fun a haA => ?_
          have hle : (a : ℤ) ≤ (N : ℤ) := by
            exact_mod_cast (Finset.mem_Icc.mp (hAsub haA)).2
          have h0 : (0 : ℤ) ≤ (a : ℤ) := Int.ofNat_nonneg a
          nlinarith [hle, h0]
      _ = (A.card : ℤ) * (N : ℤ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  obtain ⟨k, hk⟩ : ∃ k, A.card = k + 2 := ⟨A.card - 2, by omega⟩
  have hspread := sum_sq_lower V (2 ^ k)
  rw [hVcard, hVsum, hmoment] at hspread
  push_cast at hspread
  set t : ℤ := (2 : ℤ) ^ k with ht
  have htpos : (0 : ℤ) < t := by rw [ht]; positivity
  have ht1 : (1 : ℤ) ≤ t := by
    rw [ht]; exact one_le_pow₀ (by norm_num)
  have h2n : (2 : ℤ) ^ A.card = 4 * t := by rw [hk, ht]; ring
  rw [h2n] at hspread
  -- hspread : (4*t - (2*t+1)) * (t+1)^2 ≤ 4*t * Q
  have hQ' : (4 : ℤ) * t * (∑ a ∈ A, (a : ℤ) ^ 2) ≤ 4 * t * ((A.card : ℤ) * (N : ℤ) ^ 2) := by
    have h4t : (0 : ℤ) < 4 * t := by linarith
    exact mul_le_mul_of_nonneg_left hQ (le_of_lt h4t)
  have hcube : t ^ 3 ≤ 4 * t * ((A.card : ℤ) * (N : ℤ) ^ 2) := by
    nlinarith [hspread, hQ', ht1, htpos]
  have hsq : t ^ 2 ≤ 4 * ((A.card : ℤ) * (N : ℤ) ^ 2) := by
    nlinarith [hcube, htpos, ht1]
  have hgoal : (2 : ℤ) ^ (2 * A.card) = 16 * t ^ 2 := by rw [hk, ht]; ring
  have : (2 : ℤ) ^ (2 * A.card) ≤ 64 * (A.card : ℤ) * (N : ℤ) ^ 2 := by
    rw [hgoal]; nlinarith [hsq]
  exact_mod_cast this

/-- Real-valued form, matching the shape of the frozen file's `variants.weaker`. -/
theorem erdos1_sqrt_real (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N)
    (hcard : 2 ≤ A.card) :
    (2 : ℝ) ^ A.card / (8 * Real.sqrt A.card) ≤ (N : ℝ) := by
  have hnat := erdos1_sqrt N A h hcard
  have hZ : ((2 : ℝ) ^ A.card) ^ 2 ≤ 64 * (A.card : ℝ) * (N : ℝ) ^ 2 := by
    have : ((2 ^ (2 * A.card) : ℕ) : ℝ) ≤ ((64 * A.card * N ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at this
    calc ((2 : ℝ) ^ A.card) ^ 2 = (2 : ℝ) ^ (2 * A.card) := by rw [← pow_mul]; ring_nf
      _ ≤ 64 * (A.card : ℝ) * (N : ℝ) ^ 2 := this
  have hcpos : (0 : ℝ) < (A.card : ℝ) := by
    have : 0 < A.card := by omega
    exact_mod_cast this
  have hs : Real.sqrt (A.card : ℝ) > 0 := Real.sqrt_pos.mpr hcpos
  have hss : Real.sqrt (A.card : ℝ) ^ 2 = (A.card : ℝ) := Real.sq_sqrt (le_of_lt hcpos)
  have hR : (0 : ℝ) ≤ 8 * Real.sqrt (A.card : ℝ) * (N : ℝ) := by positivity
  have hP : (0 : ℝ) ≤ (2 : ℝ) ^ A.card := by positivity
  have hsq2 : ((2 : ℝ) ^ A.card) ^ 2 ≤ (8 * Real.sqrt (A.card : ℝ) * (N : ℝ)) ^ 2 := by
    have hexp : (8 * Real.sqrt (A.card : ℝ) * (N : ℝ)) ^ 2
        = 64 * (A.card : ℝ) * (N : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, hss]; ring
    rw [hexp]; exact hZ
  have key : (2 : ℝ) ^ A.card ≤ 8 * Real.sqrt (A.card : ℝ) * (N : ℝ) := by
    have h1 := Real.sqrt_le_sqrt hsq2
    rwa [Real.sqrt_sq hP, Real.sqrt_sq hR] at h1
  rw [div_le_iff₀ (by positivity)]
  calc (2 : ℝ) ^ A.card ≤ 8 * Real.sqrt (A.card : ℝ) * (N : ℝ) := key
    _ = (N : ℝ) * (8 * Real.sqrt (A.card : ℝ)) := by ring

/-! ### Explicit witnesses (finite computation certificates) -/

set_option maxRecDepth 40000 in
/-- `f(6) ≤ 24`: a 6-element sum-distinct set with maximum 24 < 32 = 2^5. -/
theorem witness6 : IsSumDistinctSet {11, 17, 20, 22, 23, 24} 24 :=
  ⟨by decide, (sumDistinct_iff _).mp (sumDistinct_of_card_image _ (by decide))⟩

set_option maxRecDepth 200000 in
/-- `f(7) ≤ 44`: a 7-element sum-distinct set with maximum 44 < 64 = 2^6. -/
theorem witness7 : IsSumDistinctSet {20, 31, 37, 40, 42, 43, 44} 44 :=
  ⟨by decide, (sumDistinct_iff _).mp (sumDistinct_of_card_image _ (by decide))⟩

end Erdos1
