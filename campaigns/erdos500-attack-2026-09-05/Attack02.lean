/-
# Erdős #500 — attack file.  Turán's hypergraph problem `ex₃(n, K₄³)`.

Target: `oracle/evidence/formalizer-sources/erdos/erdos-500.lean` (the frozen question file).
Every definition below is VERBATIM from that file.  The theorems the question file proves are
reproduced VERBATIM too, because this file must elaborate standalone.

## What this file adds (the attack)

1. `turan_construction_free` — **SEALED**.  This is one of the source's `sorry` stubs: Turán's
   explicit construction really is `K₄³`-free.  Proof: a 4-set `S` has part-profile `(a₀,a₁,a₂)`
   summing to 4, so either some part holds ≥ 3 vertices of `S` (take three of them: profile
   `(3,0,0)`, not an edge under either clause) or some part `j` holds exactly 2 while part `j-1`
   holds ≥ 1 (take those: profile 2 in `X_j`, 1 in `X_{j-1}`, and the rule demands the single
   vertex sit in `X_{j+1}`, so it is not an edge).  The arithmetic disjunction is discharged by
   `omega`; the cyclic-index facts by `decide`.

2. `ex3_four_mul_le` — **NEW, SEALED**: `4 * ex3 n ≤ 3 * n.choose 3` for `n ≥ 4`.  The first real
   upper bound in the artifact.  Double count `{(e,S) : e ∈ H, e ⊆ S, #S = 4}`: each 4-set carries
   at most 3 edges (else it IS a `K₄³`), each edge sits in `n-3` four-sets.
   ⛔ **CALIBRATION: 3/4 = 0.75 is WEAKER than Razborov's 0.5611666 and is NOT a headline.**
   `razborov_upper_bound` stays open.  Recorded honestly as `three_quarters_weaker_than_razborov`.

3. `ex3_four : ex3 4 = 3` — **NEW, SEALED** exact value.  The source header says "`ex3 4 = 3`; NOT
   formalized here".  It is now.  Upper from (2); lower from an explicit 3-edge witness.

4. `ex3_five : ex3 5 = 7` — **NEW, SEALED** exact value.  Upper from (2) (`4·8 = 32 > 30`); lower
   from Turán's own construction on 5 vertices, which (2)'s bound meets exactly.

5. `ex3_ten_mul_le` (§8b) — **NEW, SEALED**: `10 * ex3 n ≤ 7 * n.choose 3` for `n ≥ 5`, i.e.
   density `≤ 0.7`.  Sharper than (2).  Two nested double counts: inside a 5-set at least 3 of the
   10 triples are missing (`5 ≤ 2·#missing`), and each edge lies in `binom (n-3) 2` five-sets.
   ⛔ **STILL NOT A HEADLINE: `0.7 > 0.5611666`.**  `razborov_upper_bound` stays open.

6. `ex3_six : ex3 6 = 14` — **NEW, SEALED** third exact value, reachable only from (5): the `3/4`
   bound of (2) stops at `≤ 15`.  Matches `binom 6 3 - T(6,4,3) = 20 - 6` from the covering-design
   literature, and the `0.7` bound is tight here (`density 6 = 7/10`).

7. Reduction lemmas that name exactly what is left: with `turan_construction_free` sealed, the
   entire `5/9` lower bound reduces to a pure counting statement about `#(turanEdges n)`.

## What is NOT proved, and is left as `sorry`, unchanged from the source

`turan_construction_card`, `turan_lower_bound`, `razborov_upper_bound`, `turan_density_lower`,
`razborov_density_upper`.  Their `#print axioms` lines show `sorryAx` and must keep showing it.
-/
import Mathlib

namespace Erdos500

open Filter Topology

/-! ## §0  Definitions — VERBATIM from the frozen question file -/

def Is3Uniform {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = 3

def IsCompleteOn {n : ℕ} (H : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∀ e ⊆ S, e.card = 3 → e ∈ H

def ContainsK4 {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ S : Finset (Fin n), S.card = 4 ∧ IsCompleteOn H S

def IsK4Free {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ¬ ContainsK4 H

def Admissible {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  Is3Uniform H ∧ IsK4Free H

def exSet (n : ℕ) : Set ℕ :=
  {m | ∃ H : Finset (Finset (Fin n)), Admissible H ∧ H.card = m}

noncomputable def ex3 (n : ℕ) : ℕ := sSup (exSet n)

noncomputable def density (n : ℕ) : ℝ := (ex3 n : ℝ) / (n.choose 3 : ℝ)

def IsTuranDensity (c : ℝ) : Prop :=
  Tendsto (fun n : ℕ => density n) atTop (𝓝 c)

def Question : Prop :=
  ∃ c : ℝ, IsTuranDensity c

def TuranConjecture : Prop :=
  IsTuranDensity (5 / 9)

def partOf {n : ℕ} (v : Fin n) : Fin 3 :=
  ⟨(v : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩

def partCard {n : ℕ} (e : Finset (Fin n)) (j : Fin 3) : ℕ :=
  (e.filter (fun v => partOf v = j)).card

def TuranAdmissible {n : ℕ} (e : Finset (Fin n)) : Prop :=
  (∀ j : Fin 3, partCard e j = 1) ∨ (∃ j : Fin 3, partCard e j = 2 ∧ partCard e (j + 1) = 1)

instance decTuranAdmissible {n : ℕ} (e : Finset (Fin n)) : Decidable (TuranAdmissible e) := by
  unfold TuranAdmissible
  infer_instance

def turanEdges (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.powersetCard 3 (Finset.univ : Finset (Fin n))).filter TuranAdmissible

/-! ## §1  The question file's own PROVED infrastructure — reproduced VERBATIM -/

theorem subset_powersetCard {n : ℕ} {H : Finset (Finset (Fin n))} (hH : Admissible H) :
    H ⊆ Finset.powersetCard 3 (Finset.univ : Finset (Fin n)) := by
  intro e he
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hH.1 e he⟩

theorem exSet_bddAbove (n : ℕ) : BddAbove (exSet n) := by
  refine ⟨n.choose 3, ?_⟩
  rintro m ⟨H, hH, rfl⟩
  have h := Finset.card_le_card (subset_powersetCard hH)
  rwa [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h

theorem exSet_nonempty (n : ℕ) : (exSet n).Nonempty := by
  refine ⟨0, (∅ : Finset (Finset (Fin n))), ⟨?_, ?_⟩, Finset.card_empty⟩
  · intro e he
    exact absurd he (Finset.notMem_empty e)
  · rintro ⟨S, hS, hcomp⟩
    obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (s := S) (n := 3) (by omega)
    exact Finset.notMem_empty t (hcomp t hts htcard)

theorem ex3_le_choose (n : ℕ) : ex3 n ≤ n.choose 3 := by
  refine csSup_le (exSet_nonempty n) ?_
  rintro m ⟨H, hH, rfl⟩
  have hle := Finset.card_le_card (subset_powersetCard hH)
  rwa [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hle

theorem ex3_eq_choose_of_lt_four {n : ℕ} (hn : n < 4) : ex3 n = n.choose 3 := by
  refine le_antisymm (ex3_le_choose n) ?_
  have hadm : Admissible (Finset.powersetCard 3 (Finset.univ : Finset (Fin n))) := by
    refine ⟨fun e he => (Finset.mem_powersetCard.mp he).2, ?_⟩
    rintro ⟨S, hS, -⟩
    have hcard : S.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ S)
      rwa [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hmem : n.choose 3 ∈ exSet n := by
    refine ⟨Finset.powersetCard 3 (Finset.univ : Finset (Fin n)), hadm, ?_⟩
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact le_csSup (exSet_bddAbove n) hmem

theorem ex3_zero : ex3 0 = 0 := by
  rw [ex3_eq_choose_of_lt_four (by norm_num)]
  decide

theorem ex3_two : ex3 2 = 0 := by
  rw [ex3_eq_choose_of_lt_four (by norm_num)]
  decide

theorem ex3_three : ex3 3 = 1 := by
  rw [ex3_eq_choose_of_lt_four (by norm_num)]
  decide

theorem turanDensity_unique {c c' : ℝ} (h : IsTuranDensity c) (h' : IsTuranDensity c') :
    c = c' :=
  tendsto_nhds_unique h h'

theorem turanConjecture_imp_question (h : TuranConjecture) : Question :=
  ⟨5 / 9, h⟩

theorem turanEdges_is3Uniform (n : ℕ) : Is3Uniform (turanEdges n) := by
  intro e he
  rw [turanEdges, Finset.mem_filter] at he
  exact (Finset.mem_powersetCard.mp he.1).2

theorem turanEdges_card_le_ex3_of_free (n : ℕ) (hfree : IsK4Free (turanEdges n)) :
    (turanEdges n).card ≤ ex3 n :=
  le_csSup (exSet_bddAbove n) ⟨turanEdges n, ⟨turanEdges_is3Uniform n, hfree⟩, rfl⟩

theorem turan_lt_razborov : (5 : ℝ) / 9 < 0.5611666 := by
  norm_num

/-! ## §2  NEW — unfolding bridges (defeq, so `rfl`), used to keep `omega` honest -/

theorem partCard_def {n : ℕ} (e : Finset (Fin n)) (j : Fin 3) :
    partCard e j = (e.filter (fun v => partOf v = j)).card := rfl

theorem turanAdmissible_def {n : ℕ} (e : Finset (Fin n)) :
    TuranAdmissible e ↔
      ((∀ j : Fin 3, partCard e j = 1) ∨
        (∃ j : Fin 3, partCard e j = 2 ∧ partCard e (j + 1) = 1)) := Iff.rfl

/-- Every element of `Fin 3` is `j`, `j+1` or `j+2`.  Pure `decide` over 9 pairs. -/
theorem fin3_trichotomy : ∀ j j' : Fin 3, j' = j ∨ j' = j + 1 ∨ j' = j + 2 := by decide

/-- The three cyclic shifts of a part index are pairwise distinct. -/
theorem fin3_shift_ne : ∀ j : Fin 3, j + 2 ≠ j ∧ j + 1 ≠ j ∧ j + 1 ≠ j + 2 := by decide

/-! ## §3  NEW — part-count bookkeeping for Turán's construction -/

/-- If every vertex of `e` sits in part `j` then all of `e` is counted at `j`. -/
theorem partCard_of_all {n : ℕ} {e : Finset (Fin n)} {j : Fin 3}
    (h : ∀ v ∈ e, partOf v = j) : partCard e j = e.card := by
  rw [partCard_def, Finset.filter_true_of_mem h]

/-- …and nothing is counted at any other part. -/
theorem partCard_of_all_other {n : ℕ} {e : Finset (Fin n)} {j j' : Fin 3}
    (h : ∀ v ∈ e, partOf v = j) (hne : j' ≠ j) : partCard e j' = 0 := by
  rw [partCard_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v hv
  rw [h v hv]
  exact fun hh => hne hh.symm

/-- The part-profile of a set split as `A ∪ B` with `A` inside part `p` and `B` inside part `q`. -/
theorem partCard_split {n : ℕ} {A B : Finset (Fin n)} {p q : Fin 3}
    (hA : ∀ v ∈ A, partOf v = p) (hB : ∀ v ∈ B, partOf v = q) (hpq : p ≠ q) :
    partCard (A ∪ B) p = A.card ∧ partCard (A ∪ B) q = B.card ∧
      ∀ r : Fin 3, r ≠ p → r ≠ q → partCard (A ∪ B) r = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [partCard_def, Finset.filter_union]
    have h1 : A.filter (fun v => partOf v = p) = A := Finset.filter_true_of_mem hA
    have h2 : B.filter (fun v => partOf v = p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv
      rw [hB v hv]
      exact fun hh => hpq hh.symm
    rw [h1, h2, Finset.union_empty]
  · rw [partCard_def, Finset.filter_union]
    have h1 : A.filter (fun v => partOf v = q) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv
      rw [hA v hv]
      exact hpq
    have h2 : B.filter (fun v => partOf v = q) = B := Finset.filter_true_of_mem hB
    rw [h1, h2, Finset.empty_union]
  · intro r hrp hrq
    rw [partCard_def, Finset.filter_union, Finset.card_eq_zero]
    have h1 : A.filter (fun v => partOf v = r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv
      rw [hA v hv]
      exact fun hh => hrp hh.symm
    have h2 : B.filter (fun v => partOf v = r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv
      rw [hB v hv]
      exact fun hh => hrq hh.symm
    rw [h1, h2, Finset.union_empty]

/-! ## §4  NEW — the two shapes of non-edge -/

/-- Profile `(3,0,0)`: three vertices inside one part is never a Turán edge.  Clause one wants
every part-count to be `1`; clause two wants some part-count to be `2`. -/
theorem not_turanAdmissible_of_three {n : ℕ} {e : Finset (Fin n)} {j : Fin 3}
    (h : ∀ v ∈ e, partOf v = j) (hc : e.card = 3) : ¬ TuranAdmissible e := by
  intro hTA
  rw [turanAdmissible_def] at hTA
  have hj : partCard e j = 3 := by rw [partCard_of_all h, hc]
  rcases hTA with hA | ⟨j', hj'2, -⟩
  · have := hA j
    omega
  · by_cases hjj : j' = j
    · subst hjj
      omega
    · have h0 := partCard_of_all_other h hjj
      omega

/-- Profile `2` in `X_j`, `1` in `X_{j+2}`, `0` in `X_{j+1}`: not a Turán edge.  Clause one fails
because a count is `2`; clause two forces the index to be `j` (the only count-`2` part) and then
demands `partCard e (j+1) = 1`, which is `0`.  ⛔ This is exactly where the source's cyclic
asymmetry — *two in `X_i` and one in `X_{i+1}`* — does the work. -/
theorem not_turanAdmissible_of_two_one {n : ℕ} {e : Finset (Fin n)} {j : Fin 3}
    (h2 : partCard e j = 2) (h1 : partCard e (j + 2) = 1) (h0 : partCard e (j + 1) = 0) :
    ¬ TuranAdmissible e := by
  intro hTA
  rw [turanAdmissible_def] at hTA
  rcases hTA with hA | ⟨j', hj'2, hj'1⟩
  · have := hA j
    omega
  · rcases fin3_trichotomy j j' with h | h | h
    · subst h; omega
    · subst h; omega
    · subst h; omega

/-! ## §5  ⭐ SEALED — `turan_construction_free`, one of the source's `sorry` stubs -/

/-- **Turán's construction is `K₄³`-free.**  (Source stub: `turan_construction_free`.)

Let `S` be any 4-set and `a j = partCard S j`, so `a 0 + a 1 + a 2 = 4`.  Then either some
`a j ≥ 3` — take three vertices of `S` from part `j`, profile `(3,0,0)` — or some `a j = 2` with
`a (j+2) ≥ 1` — take two from `X_j` and one from `X_{j-1}`.  Neither triple obeys the source's
edge rule, so `S` is not covered by all four of its `3`-subsets. -/
theorem turan_construction_free (n : ℕ) : IsK4Free (turanEdges n) := by
  rintro ⟨S, hS, hcomp⟩
  -- the part profile of `S` sums to 4
  have hsum : ∑ j : Fin 3, partCard S j = 4 := by
    have hfib : S.card = ∑ j : Fin 3, (S.filter fun v => partOf v = j).card :=
      Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ _)
    simp only [partCard_def]
    rw [← hfib]
    exact hS
  have hsum3 : partCard S 0 + partCard S 1 + partCard S 2 = 4 := by
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  have e02 : (0 : Fin 3) + 2 = 2 := by decide
  have e12 : (1 : Fin 3) + 2 = 0 := by decide
  have e22 : (2 : Fin 3) + 2 = 1 := by decide
  -- pick the part that produces a non-edge
  have hpick : ∃ j : Fin 3,
      3 ≤ partCard S j ∨ (2 ≤ partCard S j ∧ 1 ≤ partCard S (j + 2)) := by
    by_cases c0 : 3 ≤ partCard S 0
    · exact ⟨0, Or.inl c0⟩
    by_cases c1 : 3 ≤ partCard S 1
    · exact ⟨1, Or.inl c1⟩
    by_cases c2 : 3 ≤ partCard S 2
    · exact ⟨2, Or.inl c2⟩
    by_cases d0 : 2 ≤ partCard S 0 ∧ 1 ≤ partCard S 2
    · exact ⟨0, Or.inr (by rw [e02]; exact d0)⟩
    by_cases d1 : 2 ≤ partCard S 1 ∧ 1 ≤ partCard S 0
    · exact ⟨1, Or.inr (by rw [e12]; exact d1)⟩
    refine ⟨2, Or.inr ?_⟩
    rw [e22]
    exact ⟨by omega, by omega⟩
  obtain ⟨j, hj⟩ := hpick
  rcases hj with hge | ⟨h2, h1⟩
  · -- three vertices inside one part
    rw [partCard_def] at hge
    obtain ⟨e, hesub, hecard⟩ := Finset.exists_subset_card_eq (n := 3) hge
    have hall : ∀ v ∈ e, partOf v = j := fun v hv => (Finset.mem_filter.mp (hesub hv)).2
    have hsub : e ⊆ S := hesub.trans (Finset.filter_subset _ _)
    have hmem := hcomp e hsub hecard
    rw [turanEdges, Finset.mem_filter] at hmem
    exact not_turanAdmissible_of_three hall hecard hmem.2
  · -- two vertices in `X_j` and one in `X_{j+2}`
    rw [partCard_def] at h2 h1
    obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq (n := 2) h2
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq (n := 1) h1
    have hAall : ∀ v ∈ A, partOf v = j := fun v hv => (Finset.mem_filter.mp (hAsub hv)).2
    have hBall : ∀ v ∈ B, partOf v = j + 2 := fun v hv => (Finset.mem_filter.mp (hBsub hv)).2
    have hne := fin3_shift_ne j
    have hpq : j ≠ j + 2 := fun hh => hne.1 hh.symm
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro v hvA hvB
      have ha := hAall v hvA
      have hb := hBall v hvB
      rw [ha] at hb
      exact hpq hb
    have hcard : (A ∪ B).card = 3 := by
      rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]
    have hsub : A ∪ B ⊆ S :=
      Finset.union_subset (hAsub.trans (Finset.filter_subset _ _))
        (hBsub.trans (Finset.filter_subset _ _))
    have hmem := hcomp (A ∪ B) hsub hcard
    rw [turanEdges, Finset.mem_filter] at hmem
    obtain ⟨hp, hq, hr⟩ := partCard_split hAall hBall hpq
    refine not_turanAdmissible_of_two_one (j := j) ?_ ?_ ?_ hmem.2
    · rw [hp, hAcard]
    · rw [hq, hBcard]
    · exact hr (j + 1) (fun hh => hne.2.1 hh) (fun hh => hne.2.2 hh)

/-! ## §6  NEW — the extremal number is ATTAINED, so bounds transfer to `ex3` -/

/-- `exSet n` is a nonempty bounded set of naturals, so its supremum is a member: there is an
actual extremal hypergraph.  This is what lets a bound proved for every admissible `H` become a
bound on `ex3 n` (as opposed to only `csSup_le`, which would need the bound in the other shape). -/
theorem exists_extremal (n : ℕ) :
    ∃ H : Finset (Finset (Fin n)), Admissible H ∧ H.card = ex3 n :=
  Nat.sSup_mem (exSet_nonempty n) (exSet_bddAbove n)

/-! ## §7  ⭐ SEALED — the first real upper bound: `ex3 n ≤ (3/4)·binom n 3` -/

/-- A `K₄³`-free hypergraph puts at most `3` of the `4` triples of any `4`-set into `H`.
This IS `K₄³`-freeness, counted. -/
theorem card_filter_subset_le_three {n : ℕ} {H : Finset (Finset (Fin n))} (hH : Admissible H)
    {S : Finset (Fin n)} (hS : S.card = 4) : (H.filter (fun e => e ⊆ S)).card ≤ 3 := by
  have hnc : ¬ IsCompleteOn H S := fun hc => hH.2 ⟨S, hS, hc⟩
  rw [IsCompleteOn] at hnc
  push_neg at hnc
  obtain ⟨e₀, he₀S, he₀c, he₀H⟩ := hnc
  have hsub : H.filter (fun e => e ⊆ S) ⊆ Finset.powersetCard 3 S := by
    intro e he
    rw [Finset.mem_filter] at he
    exact Finset.mem_powersetCard.mpr ⟨he.2, hH.1 e he.1⟩
  have hmem : e₀ ∈ Finset.powersetCard 3 S := Finset.mem_powersetCard.mpr ⟨he₀S, he₀c⟩
  have hnot : e₀ ∉ H.filter (fun e => e ⊆ S) := by
    rw [Finset.mem_filter]
    exact fun hh => he₀H hh.1
  have hlt : (H.filter (fun e => e ⊆ S)).card < (Finset.powersetCard 3 S).card :=
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨e₀, hmem, hnot⟩)
  rw [Finset.card_powersetCard, hS] at hlt
  have h4 : (4 : ℕ).choose 3 = 4 := by decide
  omega

/-- Each `3`-edge sits in at least `n - 3` of the `4`-sets: extend it by any outside vertex. -/
theorem card_supersets_ge {n : ℕ} {e : Finset (Fin n)} (he : e.card = 3) :
    n - 3 ≤ ((Finset.powersetCard 4 (Finset.univ : Finset (Fin n))).filter
      (fun S => e ⊆ S)).card := by
  have hc : (eᶜ).card = n - 3 := by
    rw [Finset.card_compl, Fintype.card_fin, he]
  rw [← hc]
  apply Finset.card_le_card_of_injOn (fun v => insert v e)
  · intro v hv
    have hv' : v ∉ e := Finset.mem_compl.mp (Finset.mem_coe.mp hv)
    refine Finset.mem_coe.mpr ?_
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, Finset.subset_insert _ _⟩
    rw [Finset.card_insert_of_notMem hv', he]
  · intro v hv w hw h
    have hv' : v ∉ e := Finset.mem_compl.mp (Finset.mem_coe.mp hv)
    have h' : insert v e = insert w e := h
    have hvw : v ∈ insert w e := by
      rw [← h']
      exact Finset.mem_insert_self v e
    rcases Finset.mem_insert.mp hvw with h1 | h1
    · exact h1
    · exact absurd h1 hv'

/-- **NEW, SEALED.**  Every admissible hypergraph on `n ≥ 4` vertices satisfies
`4·#H ≤ 3·binom n 3`.

Double count the incidences `{(e, S) : e ∈ H, e ⊆ S, #S = 4}`:
`#H · (n-3) ≤ binom n 4 · 3`, then `4·binom n 4 = binom n 3 · (n-3)` and cancel `n-3 > 0`. -/
theorem four_mul_card_le {n : ℕ} (hn : 4 ≤ n) {H : Finset (Finset (Fin n))} (hH : Admissible H) :
    4 * H.card ≤ 3 * n.choose 3 := by
  have key : H.card * (n - 3)
      ≤ (Finset.powersetCard 4 (Finset.univ : Finset (Fin n))).card * 3 := by
    refine Finset.card_mul_le_card_mul (fun (e S : Finset (Fin n)) => e ⊆ S) ?_ ?_
    · intro e he
      show n - 3 ≤ ((Finset.powersetCard 4 (Finset.univ : Finset (Fin n))).filter
        (fun S => e ⊆ S)).card
      exact card_supersets_ge (hH.1 e he)
    · intro S hS
      show (H.filter (fun e => e ⊆ S)).card ≤ 3
      exact card_filter_subset_le_three hH (Finset.mem_powersetCard.mp hS).2
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at key
  have h4 : n.choose 4 * 4 = n.choose 3 * (n - 3) := Nat.choose_succ_right_eq n 3
  have hmul : (4 * H.card) * (n - 3) ≤ (3 * n.choose 3) * (n - 3) := by
    calc (4 * H.card) * (n - 3) = 4 * (H.card * (n - 3)) := by ring
      _ ≤ 4 * (n.choose 4 * 3) := by omega
      _ = 3 * (n.choose 4 * 4) := by ring
      _ = 3 * (n.choose 3 * (n - 3)) := by rw [h4]
      _ = (3 * n.choose 3) * (n - 3) := by ring
  have hpos : 0 < n - 3 := by omega
  exact Nat.le_of_mul_le_mul_right hmul hpos

/-- **⭐ NEW, SEALED — the artifact's first real upper bound.**
`4 · ex₃(n, K₄³) ≤ 3 · binom n 3` for `n ≥ 4`, i.e. the density never exceeds `3/4`.

⛔ **NOT A HEADLINE.**  `3/4 = 0.75` is far WEAKER than Razborov's `0.5611666`
(`three_quarters_weaker_than_razborov`, below).  `razborov_upper_bound` stays `sorry`. -/
theorem ex3_four_mul_le (n : ℕ) (hn : 4 ≤ n) : 4 * ex3 n ≤ 3 * n.choose 3 := by
  obtain ⟨H, hH, hcard⟩ := exists_extremal n
  rw [← hcard]
  exact four_mul_card_le hn hH

/-- Recorded so the calibration cannot be misread: the bound just sealed is weaker than the one
the source credits to Razborov, which remains open here. -/
theorem three_quarters_weaker_than_razborov : (0.5611666 : ℝ) < 3 / 4 := by norm_num

/-- The density form of `ex3_four_mul_le`. -/
theorem density_le_three_quarters (n : ℕ) (hn : 4 ≤ n) : density n ≤ 3 / 4 := by
  have hnat := ex3_four_mul_le n hn
  have hpos : (0 : ℝ) < (n.choose 3 : ℝ) := by
    have h : 0 < n.choose 3 := Nat.choose_pos (by omega)
    exact_mod_cast h
  have hcast : (4 : ℝ) * (ex3 n : ℝ) ≤ 3 * (n.choose 3 : ℝ) := by exact_mod_cast hnat
  rw [density, div_le_iff₀ hpos]
  linarith

/-- The `razborov_upper_bound` SHAPE, sealed at the weaker constant `3/4`. -/
theorem ex3_upper_bound_three_quarters (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (ex3 n : ℝ) ≤ ((3 : ℝ) / 4 + ε) * (n.choose 3 : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  have hnat := ex3_four_mul_le n hn
  have hcast : (4 : ℝ) * (ex3 n : ℝ) ≤ 3 * (n.choose 3 : ℝ) := by exact_mod_cast hnat
  have hnn : (0 : ℝ) ≤ (n.choose 3 : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hε.le hnn]

/-- The `razborov_density_upper` SHAPE, sealed at the weaker constant `3/4`:
any limit of the density is at most `3/4`. -/
theorem density_upper_conditional (c : ℝ) (hc : IsTuranDensity c) : c ≤ 3 / 4 :=
  le_of_tendsto hc (by
    filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    exact density_le_three_quarters n hn)

/-! ## §8  ⭐ SEALED — two new exact values -/

/-- **⭐ NEW, SEALED.**  `ex₃(4, K₄³) = 3`.  The source header lists this value and says it is
"NOT formalized here".  Upper bound from `ex3_four_mul_le` (`4·4 = 16 > 12`); lower bound from the
explicit witness "all four triples of `Fin 4` except `{0,1,2}`", which is `K₄³`-free because the
only `4`-set is `univ` and the erased triple is missing from it. -/
theorem ex3_four : ex3 4 = 3 := by
  refine le_antisymm ?_ ?_
  · have h := ex3_four_mul_le 4 (le_refl 4)
    have hc : (4 : ℕ).choose 3 = 4 := by decide
    omega
  · have hmem34 : ({0, 1, 2} : Finset (Fin 4)) ∈
        Finset.powersetCard 3 (Finset.univ : Finset (Fin 4)) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by decide⟩
    have hadm : Admissible
        ((Finset.powersetCard 3 (Finset.univ : Finset (Fin 4))).erase {0, 1, 2}) := by
      refine ⟨?_, ?_⟩
      · intro e he
        exact (Finset.mem_powersetCard.mp (Finset.mem_of_mem_erase he)).2
      · rintro ⟨S, hS, hcomp⟩
        have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by simp [hS])
        have h3 : ({0, 1, 2} : Finset (Fin 4)) ⊆ S := by
          rw [hSuniv]
          exact Finset.subset_univ _
        have hc3 : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
        exact Finset.notMem_erase _ _ (hcomp {0, 1, 2} h3 hc3)
    have hcard : ((Finset.powersetCard 3 (Finset.univ : Finset (Fin 4))).erase
        {0, 1, 2}).card = 3 := by
      rw [Finset.card_erase_of_mem hmem34, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin]
      decide
    exact le_csSup (exSet_bddAbove 4) ⟨_, hadm, hcard⟩

/-- The sealed `3/4` bound is ATTAINED at `n = 4`: `4·3 = 3·binom 4 3`.  So `3/4` is not a lazy
overestimate of the finite truth — it is exactly right at the first vertex count where a `K₄³`
can exist at all.  (It stops being tight immediately: `4·7 = 28 < 30` at `n = 5`.) -/
theorem three_quarters_tight_at_four : 4 * ex3 4 = 3 * (4 : ℕ).choose 3 := by
  have hc : (4 : ℕ).choose 3 = 4 := by decide
  rw [ex3_four, hc]

/-- `density 4 = 3/4`. -/
theorem density_four : density 4 = 3 / 4 := by
  have hc : (4 : ℕ).choose 3 = 4 := by decide
  rw [density, ex3_four, hc]
  norm_num

/-- Turán's construction on `4` vertices: parts `{0,3}, {1}, {2}`, giving `2·1·1 + 1 = 3` edges.
An independent check that `ex3_four`'s witness count is the right one. -/
theorem turanEdges_four_card : (turanEdges 4).card = 3 := by decide

/-- Turán's construction on `5` vertices: parts `{0,3}, {1,4}, {2}`, giving
`2·2·1 + C(2,2)·2 + C(2,2)·1 = 7` edges. -/
theorem turanEdges_five_card : (turanEdges 5).card = 7 := by decide

/-- **⭐ NEW, SEALED.**  `ex₃(5, K₄³) = 7`.  The double-count bound `4·ex3 5 ≤ 30` forces
`ex3 5 ≤ 7` (since `4·8 = 32 > 30`), and Turán's own construction attains `7`.  The two meet
exactly, so `n = 5` is a point where the sealed upper bound is TIGHT. -/
theorem ex3_five : ex3 5 = 7 := by
  refine le_antisymm ?_ ?_
  · have h := ex3_four_mul_le 5 (by norm_num)
    have hc : (5 : ℕ).choose 3 = 10 := by decide
    omega
  · have h := turanEdges_card_le_ex3_of_free 5 (turan_construction_free 5)
    rw [turanEdges_five_card] at h
    exact h

/-- `density 5 = 7/10`.  The first `n` at which the density has fallen below `3/4`. -/
theorem density_five : density 5 = 7 / 10 := by
  have hc : (5 : ℕ).choose 3 = 10 := by decide
  rw [density, ex3_five, hc]
  norm_num

/-- Turán's construction on `6` vertices: three parts of size `2`, giving
`2·2·2 + 3·C(2,2)·2 = 8 + 6 = 14` edges. -/
theorem turanEdges_six_card : (turanEdges 6).card = 14 := by decide

/-- **NEW, SEALED — the exact reach of the `3/4` bound at `n = 6`:** `14 ≤ ex₃(6,K₄³) ≤ 15`.

Lower from Turán's construction; upper from `ex3_four_mul_le` (`4·16 = 64 > 60`).  Kept as the
honest record of what §7 alone can say: it leaves one edge of slack.  §8b's `5`-set averaging
bound removes that slack — see `ex3_six`, which pins the value at `14`. -/
theorem ex3_six_sandwich : 14 ≤ ex3 6 ∧ ex3 6 ≤ 15 := by
  refine ⟨?_, ?_⟩
  · have h := turanEdges_card_le_ex3_of_free 6 (turan_construction_free 6)
    rw [turanEdges_six_card] at h
    exact h
  · have h := ex3_four_mul_le 6 (by norm_num)
    have hc : (6 : ℕ).choose 3 = 20 := by decide
    omega

/-! ## §8b  ⭐ THE `5`-SET AVERAGING BOUND — `10·ex3 n ≤ 7·binom n 3`, i.e. density ≤ `0.7`

Sharper than §7's `3/4`.  Two nested double counts:

* INSIDE a `5`-set `S`, the `5` four-subsets each miss a triple and each missed triple lies in
  only `2` of them, so at least `⌈5/2⌉ = 3` of the `10` triples of `S` are missing: `≤ 7` edges.
* ACROSS `n` vertices, each edge lies in `binom (n-3) 2` five-sets, so
  `#H · binom (n-3) 2 ≤ binom n 5 · 7`, and `binom n 3 · binom (n-3) 2 = binom n 5 · 10`.

⛔ STILL NOT A HEADLINE: `0.7 > 0.5611666`.  Razborov's bound remains open.
-/

/-- A `K₄³`-free hypergraph misses at least `3` of the `10` triples inside any `5`-set. -/
theorem three_missing_in_five {n : ℕ} {H : Finset (Finset (Fin n))} (hH : Admissible H)
    {S : Finset (Fin n)} (hS : S.card = 5) :
    3 ≤ ((Finset.powersetCard 3 S) \ (H.filter (fun e => e ⊆ S))).card := by
  have key : (Finset.powersetCard 4 S).card * 1
      ≤ ((Finset.powersetCard 3 S) \ (H.filter (fun e => e ⊆ S))).card * 2 := by
    refine Finset.card_mul_le_card_mul (fun (S' e : Finset (Fin n)) => e ⊆ S') ?_ ?_
    · -- every 4-subset of `S` contains a missing triple
      intro S' hS'
      show 1 ≤ (((Finset.powersetCard 3 S) \ (H.filter (fun e => e ⊆ S))).filter
        (fun e => e ⊆ S')).card
      obtain ⟨hS'sub, hS'card⟩ := Finset.mem_powersetCard.mp hS'
      have hnc : ¬ IsCompleteOn H S' := fun hc => hH.2 ⟨S', hS'card, hc⟩
      rw [IsCompleteOn] at hnc
      push_neg at hnc
      obtain ⟨e₀, he₀S', he₀c, he₀H⟩ := hnc
      have hmemT : e₀ ∈ (Finset.powersetCard 3 S) \ (H.filter (fun e => e ⊆ S)) := by
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_powersetCard.mpr ⟨he₀S'.trans hS'sub, he₀c⟩, ?_⟩
        rw [Finset.mem_filter]
        exact fun hh => he₀H hh.1
      refine Finset.card_pos.mpr ⟨e₀, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨hmemT, he₀S'⟩
    · -- each missing triple lies in only 2 of the 4-subsets of `S`
      intro e he
      show ((Finset.powersetCard 4 S).filter (fun S' => e ⊆ S')).card ≤ 2
      obtain ⟨heS, hec⟩ := Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1
      have hcard2 : (Finset.powersetCard 1 (S \ e)).card = 2 := by
        have hse : (S \ e).card = 2 := by
          have h := Finset.card_sdiff_add_card_eq_card heS
          rw [hS, hec] at h
          omega
        rw [Finset.card_powersetCard, hse]
        decide
      rw [← hcard2]
      apply Finset.card_le_card_of_injOn (fun S' => S' \ e)
      · intro S' hS'
        rw [Finset.mem_coe, Finset.mem_filter] at hS'
        obtain ⟨hmem, hsub⟩ := hS'
        obtain ⟨hS'S, hS'c⟩ := Finset.mem_powersetCard.mp hmem
        refine Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr ⟨?_, ?_⟩)
        · exact Finset.sdiff_subset_sdiff hS'S (Finset.Subset.refl e)
        · show (S' \ e).card = 1
          have h := Finset.card_sdiff_add_card_eq_card hsub
          rw [hS'c, hec] at h
          omega
      · intro A hA B hB hAB
        rw [Finset.mem_coe, Finset.mem_filter] at hA hB
        have h1 : e ∪ (A \ e) = A := Finset.union_sdiff_of_subset hA.2
        have h2 : e ∪ (B \ e) = B := Finset.union_sdiff_of_subset hB.2
        have hAB' : A \ e = B \ e := hAB
        rw [← h1, ← h2, hAB']
  rw [Finset.card_powersetCard, hS] at key
  have h54 : (5 : ℕ).choose 4 = 5 := by decide
  omega

/-- `binom n 3 · binom (n-3) 2 = binom n 5 · 10`: choosing a `5`-set and then a triple inside it
is the same as choosing a triple and then two more vertices.  Derived from
`Nat.choose_succ_right_eq` alone, so no new identity is assumed. -/
theorem choose_three_mul_choose_two {n : ℕ} (hn : 5 ≤ n) :
    n.choose 3 * ((n - 3).choose 2) = n.choose 5 * 10 := by
  have k3 : n.choose 4 * 4 = n.choose 3 * (n - 3) := Nat.choose_succ_right_eq n 3
  have k4 : n.choose 5 * 5 = n.choose 4 * (n - 4) := Nat.choose_succ_right_eq n 4
  have k1 : (n - 3).choose 2 * 2 = (n - 3).choose 1 * ((n - 3) - 1) :=
    Nat.choose_succ_right_eq (n - 3) 1
  rw [Nat.choose_one_right] at k1
  have h2 : (n - 3) - 1 = n - 4 := by omega
  rw [h2] at k1
  have step : (n.choose 3 * ((n - 3).choose 2)) * 2 = (n.choose 5 * 10) * 2 := by
    calc (n.choose 3 * ((n - 3).choose 2)) * 2
        = n.choose 3 * ((n - 3).choose 2 * 2) := by ring
      _ = n.choose 3 * ((n - 3) * (n - 4)) := by rw [k1]
      _ = (n.choose 3 * (n - 3)) * (n - 4) := by ring
      _ = (n.choose 4 * 4) * (n - 4) := by rw [← k3]
      _ = (n.choose 4 * (n - 4)) * 4 := by ring
      _ = (n.choose 5 * 5) * 4 := by rw [← k4]
      _ = (n.choose 5 * 10) * 2 := by ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) step

/-- Each `3`-edge sits in at least `binom (n-3) 2` of the `5`-sets. -/
theorem card_supersets_five_ge {n : ℕ} {e : Finset (Fin n)} (he : e.card = 3) :
    (n - 3).choose 2 ≤ ((Finset.powersetCard 5 (Finset.univ : Finset (Fin n))).filter
      (fun S => e ⊆ S)).card := by
  have hc : (Finset.powersetCard 2 (eᶜ)).card = (n - 3).choose 2 := by
    rw [Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin, he]
  rw [← hc]
  apply Finset.card_le_card_of_injOn (fun X => e ∪ X)
  · intro X hX
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hX
    obtain ⟨hXsub, hXcard⟩ := hX
    have hdisj : Disjoint e X := by
      rw [Finset.disjoint_right]
      intro v hvX hve
      exact (Finset.mem_compl.mp (hXsub hvX)) hve
    refine Finset.mem_coe.mpr ?_
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_left⟩
    rw [Finset.card_union_of_disjoint hdisj, he, hXcard]
  · intro X hX Y hY hXY
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hX hY
    have hdX : Disjoint e X := by
      rw [Finset.disjoint_right]
      intro v hvX hve
      exact (Finset.mem_compl.mp (hX.1 hvX)) hve
    have hdY : Disjoint e Y := by
      rw [Finset.disjoint_right]
      intro v hvY hve
      exact (Finset.mem_compl.mp (hY.1 hvY)) hve
    have h1 : (e ∪ X) \ e = X := Finset.union_sdiff_cancel_left hdX
    have h2 : (e ∪ Y) \ e = Y := Finset.union_sdiff_cancel_left hdY
    have hXY' : e ∪ X = e ∪ Y := hXY
    rw [← h1, ← h2, hXY']

/-- **⭐ NEW, SEALED.**  `10·#H ≤ 7·binom n 3` for every admissible `H` on `n ≥ 5` vertices. -/
theorem ten_mul_card_le {n : ℕ} (hn : 5 ≤ n) {H : Finset (Finset (Fin n))} (hH : Admissible H) :
    10 * H.card ≤ 7 * n.choose 3 := by
  have key : H.card * ((n - 3).choose 2)
      ≤ (Finset.powersetCard 5 (Finset.univ : Finset (Fin n))).card * 7 := by
    refine Finset.card_mul_le_card_mul (fun (e S : Finset (Fin n)) => e ⊆ S) ?_ ?_
    · intro e he
      show (n - 3).choose 2 ≤ ((Finset.powersetCard 5 (Finset.univ : Finset (Fin n))).filter
        (fun S => e ⊆ S)).card
      exact card_supersets_five_ge (hH.1 e he)
    · intro S hS
      show (H.filter (fun e => e ⊆ S)).card ≤ 7
      have hS5 := (Finset.mem_powersetCard.mp hS).2
      have hsub : H.filter (fun e => e ⊆ S) ⊆ Finset.powersetCard 3 S := by
        intro e he
        rw [Finset.mem_filter] at he
        exact Finset.mem_powersetCard.mpr ⟨he.2, hH.1 e he.1⟩
      have hmiss := three_missing_in_five hH hS5
      have hsplit := Finset.card_sdiff_add_card_eq_card hsub
      rw [Finset.card_powersetCard, hS5] at hsplit
      have h10 : (5 : ℕ).choose 3 = 10 := by decide
      omega
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at key
  have hid := choose_three_mul_choose_two hn
  have hpos : 0 < (n - 3).choose 2 := Nat.choose_pos (by omega)
  have hmul : (10 * H.card) * ((n - 3).choose 2) ≤ (7 * n.choose 3) * ((n - 3).choose 2) := by
    calc (10 * H.card) * ((n - 3).choose 2)
        = 10 * (H.card * ((n - 3).choose 2)) := by ring
      _ ≤ 10 * (n.choose 5 * 7) := by omega
      _ = 7 * (n.choose 5 * 10) := by ring
      _ = 7 * (n.choose 3 * ((n - 3).choose 2)) := by rw [hid]
      _ = (7 * n.choose 3) * ((n - 3).choose 2) := by ring
  exact Nat.le_of_mul_le_mul_right hmul hpos

/-- **⭐ NEW, SEALED — the sharper upper bound.**  `10·ex₃(n,K₄³) ≤ 7·binom n 3` for `n ≥ 5`:
the density never exceeds `0.7`.  Strictly better than §7's `3/4`, still weaker than Razborov. -/
theorem ex3_ten_mul_le (n : ℕ) (hn : 5 ≤ n) : 10 * ex3 n ≤ 7 * n.choose 3 := by
  obtain ⟨H, hH, hcard⟩ := exists_extremal n
  rw [← hcard]
  exact ten_mul_card_le hn hH

theorem seven_tenths_beats_three_quarters : (7 : ℝ) / 10 < 3 / 4 := by norm_num

theorem seven_tenths_weaker_than_razborov : (0.5611666 : ℝ) < 7 / 10 := by norm_num

/-- The density form. -/
theorem density_le_seven_tenths (n : ℕ) (hn : 5 ≤ n) : density n ≤ 7 / 10 := by
  have hnat := ex3_ten_mul_le n hn
  have hpos : (0 : ℝ) < (n.choose 3 : ℝ) := by
    have h : 0 < n.choose 3 := Nat.choose_pos (by omega)
    exact_mod_cast h
  have hcast : (10 : ℝ) * (ex3 n : ℝ) ≤ 7 * (n.choose 3 : ℝ) := by exact_mod_cast hnat
  rw [density, div_le_iff₀ hpos]
  linarith

/-- The `razborov_density_upper` SHAPE, sealed at `7/10`. -/
theorem density_upper_conditional_seven_tenths (c : ℝ) (hc : IsTuranDensity c) : c ≤ 7 / 10 :=
  le_of_tendsto hc (by
    filter_upwards [Filter.eventually_ge_atTop 5] with n hn
    exact density_le_seven_tenths n hn)

/-- **⭐ NEW, SEALED — a third exact value.**  `ex₃(6, K₄³) = 14`.

Upper from `ex3_ten_mul_le` (`10·15 = 150 > 140`); lower from Turán's construction on three parts
of size `2`.  The `0.7` bound is TIGHT here, and this is exactly the value `20 - T(6,4,3) = 20-6`
recorded in the covering-design literature.  ⛔ The `3/4` bound of §7 could only reach `≤ 15`;
the `5`-set count is what closes the last edge. -/
theorem ex3_six : ex3 6 = 14 := by
  refine le_antisymm ?_ ?_
  · have h := ex3_ten_mul_le 6 (by norm_num)
    have hc : (6 : ℕ).choose 3 = 20 := by decide
    omega
  · have h := turanEdges_card_le_ex3_of_free 6 (turan_construction_free 6)
    rw [turanEdges_six_card] at h
    exact h

/-- `density 6 = 7/10` — the `0.7` bound is attained at `n = 6`. -/
theorem density_six : density 6 = 7 / 10 := by
  have hc : (6 : ℕ).choose 3 = 20 := by decide
  rw [density, ex3_six, hc]
  norm_num

/-! ## §9  ⭐ SEALED reductions — exactly what the `5/9` lower bound still needs -/

/-- **⭐ NEW, SEALED.**  With `turan_construction_free` proved, the whole `5/9` lower bound reduces
to a PURE COUNTING statement about `#(turanEdges n)`: no combinatorics remains, only the
evaluation of `n₀n₁n₂ + Σ_j C(n_j,2)·n_{j+1}` against `binom n 3`.

This lemma has clean axioms; it is the honest statement of what is left. -/
theorem turan_lower_bound_of_construction_card
    (hcard : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ((5 : ℝ) / 9 - ε) * (n.choose 3 : ℝ) ≤ ((turanEdges n).card : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((5 : ℝ) / 9 - ε) * (n.choose 3 : ℝ) ≤ (ex3 n : ℝ) := by
  filter_upwards [hcard ε hε] with n hn
  have h := turanEdges_card_le_ex3_of_free n (turan_construction_free n)
  have hc : ((turanEdges n).card : ℝ) ≤ (ex3 n : ℝ) := by exact_mod_cast h
  linarith

/-- **⭐ NEW, SEALED.**  The unconditional lower bound implies the conditional density form. -/
theorem turan_density_lower_of_bound
    (hlb : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ((5 : ℝ) / 9 - ε) * (n.choose 3 : ℝ) ≤ (ex3 n : ℝ))
    (c : ℝ) (hc : IsTuranDensity c) : (5 : ℝ) / 9 ≤ c := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have h1 : ∀ᶠ n : ℕ in atTop, (5 : ℝ) / 9 - ε ≤ density n := by
    filter_upwards [hlb ε hε, Filter.eventually_ge_atTop 3] with n hn hn3
    have hpos : (0 : ℝ) < (n.choose 3 : ℝ) := by
      have h : 0 < n.choose 3 := Nat.choose_pos hn3
      exact_mod_cast h
    rw [density, le_div_iff₀ hpos]
    exact hn
  have h2 : (5 : ℝ) / 9 - ε ≤ c := ge_of_tendsto hc h1
  linarith

/-- **⭐ NEW, SEALED.**  Symmetrically for the upper side. -/
theorem razborov_density_upper_of_bound
    (hub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (ex3 n : ℝ) ≤ (0.5611666 + ε) * (n.choose 3 : ℝ))
    (c : ℝ) (hc : IsTuranDensity c) : c ≤ 0.5611666 := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have h1 : ∀ᶠ n : ℕ in atTop, density n ≤ 0.5611666 + ε := by
    filter_upwards [hub ε hε, Filter.eventually_ge_atTop 3] with n hn hn3
    have hpos : (0 : ℝ) < (n.choose 3 : ℝ) := by
      have h : 0 < n.choose 3 := Nat.choose_pos hn3
      exact_mod_cast h
    rw [density, div_le_iff₀ hpos]
    exact hn
  exact le_of_tendsto hc h1

/-! ## §10  The stubs that remain OPEN — unchanged from the source, `sorry` intact -/

/-- **STILL OPEN — pure counting.**  `#(turanEdges n) ≥ (5/9 - ε)·binom n 3` eventually. -/
theorem turan_construction_card (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((5 : ℝ) / 9 - ε) * (n.choose 3 : ℝ) ≤ ((turanEdges n).card : ℝ) := by
  sorry

/-- **STILL OPEN**, but now depending on NOTHING except `turan_construction_card`: the
combinatorial half is sealed above. -/
theorem turan_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((5 : ℝ) / 9 - ε) * (n.choose 3 : ℝ) ≤ (ex3 n : ℝ) :=
  turan_lower_bound_of_construction_card (fun δ hδ => turan_construction_card δ hδ) ε hε

/-- **STILL OPEN — Razborov's flag-algebra bound.**  Not attacked here; the sealed
`ex3_upper_bound_three_quarters` gives only `3/4`. -/
theorem razborov_upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (ex3 n : ℝ) ≤ (0.5611666 + ε) * (n.choose 3 : ℝ) := by
  sorry

/-- **STILL OPEN** — reduces to `turan_lower_bound` by the sealed
`turan_density_lower_of_bound`. -/
theorem turan_density_lower (c : ℝ) (hc : IsTuranDensity c) : (5 : ℝ) / 9 ≤ c :=
  turan_density_lower_of_bound (fun δ hδ => turan_lower_bound δ hδ) c hc

/-- **STILL OPEN** — reduces to `razborov_upper_bound` by the sealed
`razborov_density_upper_of_bound`. -/
theorem razborov_density_upper (c : ℝ) (hc : IsTuranDensity c) : c ≤ 0.5611666 :=
  razborov_density_upper_of_bound (fun δ hδ => razborov_upper_bound δ hδ) c hc

end Erdos500

-- ⛔ FOOTPRINTS.  Clean is [propext, Classical.choice, Quot.sound].
-- `sorryAx` means NOT PROVED and is expected on exactly the five open stubs and their two
-- reductions.  Everything else must be clean.

-- --- reproduced from the source (were already proved there) ---
#print axioms Erdos500.subset_powersetCard
#print axioms Erdos500.exSet_bddAbove
#print axioms Erdos500.exSet_nonempty
#print axioms Erdos500.ex3_le_choose
#print axioms Erdos500.ex3_eq_choose_of_lt_four
#print axioms Erdos500.ex3_zero
#print axioms Erdos500.ex3_two
#print axioms Erdos500.ex3_three
#print axioms Erdos500.turanDensity_unique
#print axioms Erdos500.turanConjecture_imp_question
#print axioms Erdos500.turanEdges_is3Uniform
#print axioms Erdos500.turanEdges_card_le_ex3_of_free
#print axioms Erdos500.turan_lt_razborov

-- --- NEW: infrastructure ---
#print axioms Erdos500.fin3_trichotomy
#print axioms Erdos500.fin3_shift_ne
#print axioms Erdos500.partCard_of_all
#print axioms Erdos500.partCard_of_all_other
#print axioms Erdos500.partCard_split
#print axioms Erdos500.not_turanAdmissible_of_three
#print axioms Erdos500.not_turanAdmissible_of_two_one
#print axioms Erdos500.exists_extremal
#print axioms Erdos500.card_filter_subset_le_three
#print axioms Erdos500.card_supersets_ge
#print axioms Erdos500.four_mul_card_le

-- --- NEW: ⭐ THE SEALED RESULTS ---
#print axioms Erdos500.turan_construction_free
#print axioms Erdos500.ex3_four_mul_le
#print axioms Erdos500.three_quarters_weaker_than_razborov
#print axioms Erdos500.density_le_three_quarters
#print axioms Erdos500.ex3_upper_bound_three_quarters
#print axioms Erdos500.density_upper_conditional
#print axioms Erdos500.ex3_four
#print axioms Erdos500.three_quarters_tight_at_four
#print axioms Erdos500.density_four
#print axioms Erdos500.turanEdges_four_card
#print axioms Erdos500.turanEdges_five_card
#print axioms Erdos500.ex3_five
#print axioms Erdos500.density_five
#print axioms Erdos500.turanEdges_six_card
#print axioms Erdos500.ex3_six_sandwich

-- --- NEW: ⭐ the 5-set averaging bound (0.7) and the third exact value ---
#print axioms Erdos500.three_missing_in_five
#print axioms Erdos500.choose_three_mul_choose_two
#print axioms Erdos500.card_supersets_five_ge
#print axioms Erdos500.ten_mul_card_le
#print axioms Erdos500.ex3_ten_mul_le
#print axioms Erdos500.seven_tenths_beats_three_quarters
#print axioms Erdos500.seven_tenths_weaker_than_razborov
#print axioms Erdos500.density_le_seven_tenths
#print axioms Erdos500.density_upper_conditional_seven_tenths
#print axioms Erdos500.ex3_six
#print axioms Erdos500.density_six
#print axioms Erdos500.turan_lower_bound_of_construction_card
#print axioms Erdos500.turan_density_lower_of_bound
#print axioms Erdos500.razborov_density_upper_of_bound

-- --- STILL OPEN: these MUST show sorryAx ---
#print axioms Erdos500.turan_construction_card
#print axioms Erdos500.turan_lower_bound
#print axioms Erdos500.razborov_upper_bound
#print axioms Erdos500.turan_density_lower
#print axioms Erdos500.razborov_density_upper
