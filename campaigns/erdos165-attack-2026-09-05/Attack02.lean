/-
# Erdős #165 — ATTACK FILE 02 (2026-09-05) · SHEARER'S ARGUMENT

Target row: `erdos:165`. Frozen spec: `oracle/evidence/formalizer-sources/erdos/erdos-165.lean`
(NOT modified, NOT imported). Predecessor: `Attack01.lean` (46 sealed declarations, exit 0).

Attack01 proved `conjecture_c_eq_half_iff_upper_of_hhkp`: granting the published HHKP lower
bound, the ENTIRE remaining content of TARGET 3 is the upper bound
`R(3,k) ≤ (1/2 + o(1))·k²/log k`. Attack01's OBSTRUCTION 2 was Shearer's upper bound with
constant `1` — unformalized, carried as a bare hypothesis on every statement needing it.

⛔ THIS FILE CLOSES NOTHING ABOUT THE OPEN PROBLEM. `R(3,k) ~ c·k²/log k` is open and the
constant remains pinned only to `[1/2, 1]`. Shearer's theorem is PUBLISHED (Shearer 1983);
there is no novelty here. What this file does is:

  (a) PROVE, unconditionally, the combinatorial skeleton of Shearer's argument — the
      neighbourhood-independence step, the greedy (Caro–Wei) extraction, and the degree
      dichotomy — and run that skeleton to completion at the TRIVIAL independence input
      `1/(D+1)`, obtaining `R(3,k) ≤ k²` with no hypotheses at all;
  (b) DISCHARGE Attack01's OBSTRUCTION 4 as a corollary: `(RamseySet 3 k).Nonempty` for every
      `k`, so the five Attack01 statements that carried Ramsey's theorem as a hypothesis are
      restated here unconditionally;
  (c) CLOSE Attack01's OBSTRUCTION 5: `R(3,3) = 6`, exactly, by the neighbourhood pigeonhole;
  (d) do the FUNCTION ANALYSIS of Shearer's `f(x) = (x log x − x + 1)/(x−1)²` — a two-sided
      sandwich `(log x − 1)/(x−1) < f(x) < log x/(x−1)` pinning `f(x) ~ log x / x`, and the
      strict comparison `1/(x+1) < f(x)` beyond `x = e²` which is exactly the statement that
      Shearer's input beats Caro–Wei's;
  (e) SPLIT OBSTRUCTION 2 in two, and CLOSE THE ELEMENTARY HALF. Shearer's asymptotic Ramsey
      bound is decomposed into (i) `ShearerBound`, his FINITE independence inequality, carried
      as an explicit hypothesis, and (ii) `shearer_estimate`, an elementary calculus statement
      about `f` and `log` alone — and (ii) is PROVED here (§7), not assumed. Consequently
      `shearer_upper_of_bound` derives `R(3,k) ≤ (1+o(1))k²/log k` from `ShearerBound` and
      NOTHING ELSE. Attack01 carried that whole asymptotic as one opaque hypothesis; what is
      left unformalized is now a single 1983 combinatorial inequality.

A hypothesis is honest; a `sorry` is a fabricated result wearing a theorem's clothes.
This file contains no `sorry`.

Definitions in §0 and the lemmas marked ⟪A01⟫ are copied VERBATIM from Attack01 (sealed there,
recopied so this file compiles standalone). Everything marked **NEW** is new in Attack02.
-/

import Mathlib
open Filter Topology Finset

namespace Erdos165

/-! ## §0. Definitions — VERBATIM from the frozen spec. -/

/-- `IsRamseyBound s t n` : every red/blue colouring of the edges of `K_n` contains a red `K_s`
or a blue `K_t`. VERBATIM from the spec. -/
def IsRamseyBound (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t

/-- VERBATIM from the spec. -/
def RamseySet (s t : ℕ) : Set ℕ := {n | IsRamseyBound s t n}

/-- VERBATIM from the spec. -/
noncomputable def R (s t : ℕ) : ℕ := sInf (RamseySet s t)

/-- VERBATIM from the spec. -/
noncomputable def scale (k : ℕ) : ℝ := (k : ℝ) ^ 2 / Real.log k

/-- TARGET 1. VERBATIM from the spec. -/
def Question : Prop :=
  ∃ c : ℝ, Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c)

/-- TARGET 3. VERBATIM from the spec. -/
def Conjecture_c_eq_half : Prop :=
  Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 ((1 : ℝ) / 2))

/-! ## §1. Attack01 carry-over. Sealed in Attack01; recopied verbatim so this file stands alone. -/

/-- ⟪A01⟫ No graph is `0`-clique-free. -/
theorem not_cliqueFree_zero {V : Type*} (G : SimpleGraph V) : ¬ G.CliqueFree 0 := by
  intro h
  exact h ∅ ⟨by simp [SimpleGraph.IsClique], by simp⟩

/-- ⟪A01⟫ The forcing condition is vacuous when the blue parameter is `0`. -/
theorem isRamseyBound_zero_right (s n : ℕ) : IsRamseyBound s 0 n :=
  fun _ => Or.inr (not_cliqueFree_zero _)

/-- ⟪A01⟫ Clique-freeness pulls back along an injection. -/
theorem cliqueFree_comap {V W : Type*} (f : V ↪ W) {H : SimpleGraph W} {r : ℕ}
    (hH : H.CliqueFree r) : (SimpleGraph.comap (⇑f) H).CliqueFree r := by
  intro t ht
  refine hH (t.map f) ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_map, Set.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hne : a' ≠ b' := fun h => hab (by rw [h])
    exact SimpleGraph.comap_adj.mp (ht.1 ha' hb' hne)
  · rw [Finset.card_map]
    exact ht.2

/-- ⟪A01⟫ `IsRamseyBound s t ·` is upward closed in the vertex count. -/
theorem isRamseyBound_mono_n {s t n m : ℕ} (hnm : n ≤ m) (hb : IsRamseyBound s t n) :
    IsRamseyBound s t m := by
  intro G
  have hcompl : (SimpleGraph.comap (⇑(Fin.castLEEmb hnm)) G)ᶜ
      = SimpleGraph.comap (⇑(Fin.castLEEmb hnm)) Gᶜ := by
    ext a b
    simp [SimpleGraph.comap_adj, SimpleGraph.compl_adj]
  rcases hb (SimpleGraph.comap (⇑(Fin.castLEEmb hnm)) G) with h1 | h1
  · exact Or.inl fun hcf => h1 (cliqueFree_comap (Fin.castLEEmb hnm) hcf)
  · refine Or.inr fun hcf => h1 ?_
    rw [hcompl]
    exact cliqueFree_comap (Fin.castLEEmb hnm) hcf

/-- ⟪A01⟫ -/
theorem R_le_iff_of_nonempty {s t n : ℕ} (hne : (RamseySet s t).Nonempty) :
    R s t ≤ n ↔ IsRamseyBound s t n :=
  ⟨fun h => isRamseyBound_mono_n h (Nat.sInf_mem hne), fun h => Nat.sInf_le h⟩

/-- ⟪A01⟫ -/
theorem lt_R_of_not_isRamseyBound {s t n : ℕ} (h : ¬ IsRamseyBound s t n)
    (hne : (RamseySet s t).Nonempty) : n < R s t := by
  by_contra hcon
  push_neg at hcon
  exact h (isRamseyBound_mono_n hcon (Nat.sInf_mem hne))

/-- ⟪A01⟫ The shape of every Ramsey lower bound. -/
theorem lt_R_of_witness {k n : ℕ} (G : SimpleGraph (Fin n))
    (htri : G.CliqueFree 3) (hind : Gᶜ.CliqueFree k)
    (hne : (RamseySet 3 k).Nonempty) : n < R 3 k := by
  refine lt_R_of_not_isRamseyBound (fun h => ?_) hne
  rcases h G with h1 | h1
  · exact h1 htri
  · exact h1 hind

/-- ⟪A01⟫ -/
theorem not_mem_RamseySet_of_lt {k n : ℕ} (h : n < k) : n ∉ RamseySet 3 k := by
  intro hn
  rcases hn ⊥ with h1 | h1
  · exact h1 (SimpleGraph.cliqueFree_bot (by norm_num))
  · refine h1 ?_
    rw [compl_bot]
    exact SimpleGraph.cliqueFree_of_card_lt (by simpa using h)

/-- ⟪A01⟫ -/
theorem le_R_of_nonempty {k : ℕ} (hne : (RamseySet 3 k).Nonempty) : k ≤ R 3 k := by
  by_contra hcon
  push_neg at hcon
  exact not_mem_RamseySet_of_lt hcon (Nat.sInf_mem hne)

/-- ⟪A01⟫ The 5-cycle: the classical Ramsey witness. -/
def C5 : SimpleGraph (Fin 5) where
  Adj a b := a + 1 = b ∨ b + 1 = a
  symm := by
    intro a b h
    exact h.symm
  loopless := ⟨by decide⟩

instance : DecidableRel C5.Adj := fun a b =>
  inferInstanceAs (Decidable (a + 1 = b ∨ b + 1 = a))

instance : DecidableRel C5ᶜ.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ¬ C5.Adj a b))

/-- ⟪A01⟫ -/
theorem C5_triangleFree : C5.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.2
  have h1 : C5.Adj a b := ht.1 (by simp) (by simp) hab
  have h2 : C5.Adj a c := ht.1 (by simp) (by simp) hac
  have h3 : C5.Adj b c := ht.1 (by simp) (by simp) hbc
  revert hab hac hbc h1 h2 h3
  revert a b c
  decide

/-- ⟪A01⟫ -/
theorem C5_compl_cliqueFree_three : C5ᶜ.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.2
  have h1 : C5ᶜ.Adj a b := ht.1 (by simp) (by simp) hab
  have h2 : C5ᶜ.Adj a c := ht.1 (by simp) (by simp) hac
  have h3 : C5ᶜ.Adj b c := ht.1 (by simp) (by simp) hbc
  revert hab hac hbc h1 h2 h3
  revert a b c
  decide

/-- ⟪A01⟫ -/
theorem six_le_R_three_three (hne : (RamseySet 3 3).Nonempty) : 6 ≤ R 3 3 :=
  lt_R_of_witness C5 C5_triangleFree C5_compl_cliqueFree_three hne

/-- ⟪A01⟫ -/
theorem log_nat_pos {k : ℕ} (hk : 2 ≤ k) : 0 < Real.log k := by
  have hk1 : (1 : ℕ) < k := hk
  exact Real.log_pos (by exact_mod_cast hk1)

/-- ⟪A01⟫ -/
theorem sq_nat_pos {k : ℕ} (hk : 2 ≤ k) : (0 : ℝ) < (k : ℝ) ^ 2 := by
  have hk0 : (0 : ℕ) < k := by omega
  have hk0' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  exact pow_pos hk0' 2

/-- ⟪A01⟫ -/
theorem scale_pos {k : ℕ} (hk : 2 ≤ k) : 0 < scale k :=
  div_pos (sq_nat_pos hk) (log_nat_pos hk)

/-- ⟪A01⟫ -/
theorem scale_mul_log {k : ℕ} (hk : 2 ≤ k) : scale k * Real.log k = (k : ℝ) ^ 2 := by
  have hL : Real.log k ≠ 0 := ne_of_gt (log_nat_pos hk)
  rw [scale]
  field_simp

/-- ⟪A01⟫ -/
theorem le_ratio_of_le_scale {a : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (h : a * scale k ≤ (R 3 k : ℝ)) :
    a ≤ (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 := by
  have hL : 0 < Real.log k := log_nat_pos hk
  have hK : (0 : ℝ) < (k : ℝ) ^ 2 := sq_nat_pos hk
  rw [le_div_iff₀ hK]
  calc a * (k : ℝ) ^ 2 = a * (scale k * Real.log k) := by rw [scale_mul_log hk]
    _ = a * scale k * Real.log k := by ring
    _ ≤ (R 3 k : ℝ) * Real.log k := mul_le_mul_of_nonneg_right h hL.le

/-- ⟪A01⟫ -/
theorem ratio_le_of_scale_le {b : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (h : (R 3 k : ℝ) ≤ b * scale k) :
    (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 ≤ b := by
  have hL : 0 < Real.log k := log_nat_pos hk
  have hK : (0 : ℝ) < (k : ℝ) ^ 2 := sq_nat_pos hk
  rw [div_le_iff₀ hK]
  calc (R 3 k : ℝ) * Real.log k ≤ b * scale k * Real.log k :=
        mul_le_mul_of_nonneg_right h hL.le
    _ = b * (scale k * Real.log k) := by ring
    _ = b * (k : ℝ) ^ 2 := by rw [scale_mul_log hk]

/-- ⟪A01⟫ -/
theorem limit_ge_of_lower_bound {c₀ c : ℝ}
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c₀ - ε) * scale k ≤ (R 3 k : ℝ))
    (hc : Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c)) :
    c₀ ≤ c := by
  by_contra hcon
  push_neg at hcon
  have hε : 0 < (c₀ - c) / 2 := by linarith
  have hev : ∀ᶠ k : ℕ in atTop,
      c₀ - (c₀ - c) / 2 ≤ (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 := by
    filter_upwards [hlow ((c₀ - c) / 2) hε, eventually_ge_atTop 2] with k h1 h2
    exact le_ratio_of_le_scale h2 h1
  have hle := ge_of_tendsto hc hev
  linarith

/-- ⟪A01⟫ -/
theorem limit_le_of_upper_bound {c₁ c : ℝ}
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (c₁ + ε) * scale k)
    (hc : Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c)) :
    c ≤ c₁ := by
  by_contra hcon
  push_neg at hcon
  have hε : 0 < (c - c₁) / 2 := by linarith
  have hev : ∀ᶠ k : ℕ in atTop,
      (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 ≤ c₁ + (c - c₁) / 2 := by
    filter_upwards [hup ((c - c₁) / 2) hε, eventually_ge_atTop 2] with k h1 h2
    exact ratio_le_of_scale_le h2 h1
  have hle := le_of_tendsto hc hev
  linarith

/-! ## §2. **NEW** — independence, and the bridge to the spec's `Gᶜ.CliqueFree`.

Shearer's argument is about independent sets; the spec's `R` is about cliques in the
complement. These four lemmas are the translation, and nothing below uses any containment or
independence API from Mathlib — the predicate is defined here so no revision drift can reach it. -/

/-- **NEW.** `s` is an independent set of `G`. -/
def IsIndep {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ G.Adj a b

/-- **NEW.** Independence in `G` is exactly cliqueness in `Gᶜ`. -/
theorem isIndep_iff_compl_isClique {V : Type*} (G : SimpleGraph V) (s : Finset V) :
    IsIndep G s ↔ Gᶜ.IsClique (s : Set V) := by
  constructor
  · intro h a ha b hb hab
    exact ⟨hab, h a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab⟩
  · intro h a ha b hb hab
    exact (h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab).2

/-- **NEW.** Independence passes to subsets. -/
theorem IsIndep.subset {V : Type*} {G : SimpleGraph V} {s u : Finset V} (hs : IsIndep G s)
    (hus : u ⊆ s) : IsIndep G u :=
  fun a ha b hb hab => hs a (hus ha) b (hus hb) hab

/-- **NEW — the bridge.** An independent set of size at least `k` kills `Gᶜ.CliqueFree k`.
This is the step that turns any independence-number lower bound into a Ramsey upper bound. -/
theorem not_cliqueFree_compl_of_indep {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s : Finset V} {k : ℕ} (hs : IsIndep G s) (hk : k ≤ s.card) : ¬ Gᶜ.CliqueFree k := by
  obtain ⟨u, hus, hu⟩ : ∃ u ⊆ s, u.card = k := Finset.exists_subset_card_eq hk
  intro hcf
  exact hcf u ⟨(isIndep_iff_compl_isClique G u).mp (hs.subset hus), hu⟩

/-! ## §3. **NEW** — the combinatorial heart of Shearer's argument.

Two steps, both proved unconditionally:
  (1) in a triangle-free graph the neighbourhood of EVERY vertex is an independent set;
  (2) a greedy extraction: if every neighbourhood has at most `D` elements, some independent
      set has at least `n/(D+1)` elements.
Step (1) is the step Shearer's induction turns on. Step (2) is the Caro–Wei input; Shearer's
theorem replaces its `1/(D+1)` by `f(D) ≈ log D / D`, and that replacement is the whole
improvement from `k²` to `k²/log k`. -/

/-- **NEW.** Three mutually adjacent vertices form a triangle. -/
theorem three_clique_of_adj {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : G.IsNClique 3 {a, b, c} := by
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | exact hab
        | exact hac
        | exact hbc
        | exact hab.symm
        | exact hac.symm
        | exact hbc.symm
  · exact Finset.card_eq_three.mpr ⟨a, b, c, hab.ne, hac.ne, hbc.ne, rfl⟩

/-- **NEW — STEP (1) OF SHEARER'S ARGUMENT.** In a triangle-free graph the neighbourhood of a
vertex is independent: two adjacent neighbours of `v` would close a triangle through `v`.
The neighbourhood is supplied as an arbitrary function `N` with `w ∈ N v ↔ G.Adj v w`, so the
lemma needs no `DecidableRel` instance and applies verbatim to `G` and to `Gᶜ`. -/
theorem indep_neighborhood {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (htf : G.CliqueFree 3) {N : V → Finset V} (hN : ∀ v w, w ∈ N v ↔ G.Adj v w) (v : V) :
    IsIndep G (N v) := by
  intro a ha b hb hab hadj
  exact htf {v, a, b} (three_clique_of_adj ((hN v a).mp ha) ((hN v b).mp hb) hadj)

/-- **NEW — STEP (2), the greedy/Caro–Wei extraction.** If every vertex's neighbourhood is
covered by a set of size at most `D`, then every finite vertex set `t` contains an independent
set `s` with `|t| ≤ (D+1)·|s|`. Proved by induction on a bound for `|t|`: take any `v ∈ t`,
delete `v` and its cover, recurse, and re-insert `v`. -/
theorem exists_indep_of_cover {V : Type*} [DecidableEq V] (G : SimpleGraph V) (D : ℕ)
    (N : V → Finset V) (hN : ∀ v w : V, G.Adj v w → w ∈ N v) (hD : ∀ v, (N v).card ≤ D) :
    ∀ t : Finset V, ∃ s ⊆ t, IsIndep G s ∧ t.card ≤ (D + 1) * s.card := by
  suffices H : ∀ m : ℕ, ∀ t : Finset V, t.card ≤ m →
      ∃ s ⊆ t, IsIndep G s ∧ t.card ≤ (D + 1) * s.card by
    intro t
    exact H t.card t le_rfl
  intro m
  induction m with
  | zero =>
      intro t ht
      have h0 : t.card = 0 := Nat.le_zero.mp ht
      refine ⟨∅, Finset.empty_subset t, ?_, by simp [h0]⟩
      intro a ha
      simp at ha
  | succ m ih =>
      intro t ht
      rcases Finset.eq_empty_or_nonempty t with rfl | ⟨v, hv⟩
      · refine ⟨∅, Finset.empty_subset _, ?_, by simp⟩
        intro a ha
        simp at ha
      · obtain ⟨u, hu⟩ : ∃ u : Finset V, u = insert v (N v) := ⟨_, rfl⟩
        obtain ⟨t', ht'⟩ : ∃ t' : Finset V, t' = t \ u := ⟨_, rfl⟩
        have hmemu : ∀ x, x ∈ u ↔ (x = v ∨ x ∈ N v) := by
          intro x; rw [hu]; exact Finset.mem_insert
        have hmemt' : ∀ x, x ∈ t' ↔ (x ∈ t ∧ x ∉ u) := by
          intro x; rw [ht']; exact Finset.mem_sdiff
        have hucard : u.card ≤ D + 1 := by
          rw [hu]
          exact le_trans (Finset.card_insert_le v (N v)) (Nat.add_le_add_right (hD v) 1)
        have ht'sub : t' ⊆ t := fun x hx => ((hmemt' x).mp hx).1
        have hsub_erase : t' ⊆ t.erase v := by
          intro x hx
          obtain ⟨hxt, hxu⟩ := (hmemt' x).mp hx
          refine Finset.mem_erase.mpr ⟨?_, hxt⟩
          intro hxv
          exact hxu ((hmemu x).mpr (Or.inl hxv))
        have ht'm : t'.card ≤ m := by
          have h1 : t'.card ≤ (t.erase v).card := Finset.card_le_card hsub_erase
          have h2 : (t.erase v).card = t.card - 1 := Finset.card_erase_of_mem hv
          omega
        obtain ⟨s', hs't, hs'i, hs'c⟩ := ih t' ht'm
        have hvt' : v ∉ t' := by
          intro hx
          exact ((hmemt' v).mp hx).2 ((hmemu v).mpr (Or.inl rfl))
        have hvs' : v ∉ s' := fun hx => hvt' (hs't hx)
        refine ⟨insert v s', ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hv
          · exact ht'sub (hs't hx')
        · intro a ha b hb hab hadj
          rcases Finset.mem_insert.mp ha with rfl | ha'
          · have hb' : b ∈ s' := by
              rcases Finset.mem_insert.mp hb with rfl | h
              · exact absurd rfl hab
              · exact h
            exact ((hmemt' b).mp (hs't hb')).2 ((hmemu b).mpr (Or.inr (hN _ _ hadj)))
          · rcases Finset.mem_insert.mp hb with rfl | hb'
            · exact ((hmemt' a).mp (hs't ha')).2 ((hmemu a).mpr (Or.inr (hN _ _ hadj.symm)))
            · exact hs'i a ha' b hb' hab hadj
        · have hcard : (insert v s').card = s'.card + 1 := by
            first
              | simp [hvs']
              | exact Finset.card_insert_of_notMem hvs'
          have hcov : t.card ≤ t'.card + u.card := by
            have hsubu : t ⊆ t' ∪ u := by
              intro x hx
              by_cases h : x ∈ u
              · exact Finset.mem_union_right _ h
              · exact Finset.mem_union_left _ ((hmemt' x).mpr ⟨hx, h⟩)
            exact le_trans (Finset.card_le_card hsubu) (Finset.card_union_le _ _)
          rw [hcard]
          calc t.card ≤ t'.card + u.card := hcov
            _ ≤ (D + 1) * s'.card + (D + 1) := Nat.add_le_add hs'c hucard
            _ = (D + 1) * (s'.card + 1) := by ring

/-! ## §4. **NEW** — the skeleton run to completion, and `R(3,k) ≤ k²` unconditionally.

The dichotomy: in a triangle-free graph with no independent `k`-set, EVERY neighbourhood is
independent, hence has fewer than `k` vertices (step 1); so the maximum degree is below `k` and
greedy (step 2) yields an independent set of size at least `n/k`; that too is below `k`, so
`n < k²`. This is Shearer's argument with the trivial independence input. -/

/-- **NEW — THE SKELETON.** A triangle-free graph on `n` vertices whose independent sets all
have fewer than `k` elements has `n < k²`. -/
theorem card_lt_of_triangleFree_of_indep_lt {n k : ℕ} (hk : 1 ≤ k)
    (G : SimpleGraph (Fin n)) (htf : G.CliqueFree 3)
    (hind : ∀ s : Finset (Fin n), IsIndep G s → s.card < k) :
    n < k * k := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Fin n → Finset (Fin n), ∀ v w, w ∈ N v ↔ G.Adj v w :=
    ⟨fun v => Finset.univ.filter (fun w => G.Adj v w), by intro v w; simp⟩
  have hNcard : ∀ v, (N v).card ≤ k - 1 := by
    intro v
    have hlt := hind _ (indep_neighborhood htf hN v)
    omega
  obtain ⟨s, _, hsi, hsc⟩ :=
    exists_indep_of_cover G (k - 1) N (fun v w h => (hN v w).mpr h) hNcard Finset.univ
  rw [Finset.card_fin] at hsc
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at hsc
  have hsk : s.card < k := hind s hsi
  have hkpos : 0 < k := hk
  calc n ≤ k * s.card := hsc
    _ ≤ k * (k - 1) := Nat.mul_le_mul (le_refl k) (by omega)
    _ < k * k := mul_lt_mul_of_pos_left (by omega) hkpos

/-- **NEW — THE INTERFACE.** Any guarantee that triangle-free graphs on `n` vertices contain an
independent `k`-set is a Ramsey upper bound. This is the socket Shearer's theorem plugs into,
and it is proved unconditionally. -/
theorem R_three_le_of_indep_guarantee {k n : ℕ}
    (h : ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
      ∃ s : Finset (Fin n), IsIndep G s ∧ k ≤ s.card) :
    R 3 k ≤ n := by
  refine Nat.sInf_le ?_
  intro G
  by_cases htf : G.CliqueFree 3
  · obtain ⟨s, hs, hcard⟩ := h G htf
    exact Or.inr (not_cliqueFree_compl_of_indep hs hcard)
  · exact Or.inl htf

/-- **NEW — UNCONDITIONAL.** `k²` vertices force a triangle or an independent `k`-set. -/
theorem isRamseyBound_three_sq (k : ℕ) : IsRamseyBound 3 k (k * k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : (0 : ℕ) * 0 = 0 := by norm_num
    rw [h0]
    exact isRamseyBound_zero_right 3 0
  · intro G
    by_cases htf : G.CliqueFree 3
    · refine Or.inr ?_
      intro hcf
      have hind : ∀ s : Finset (Fin (k * k)), IsIndep G s → s.card < k := by
        intro s hs
        by_contra hcon
        push_neg at hcon
        exact not_cliqueFree_compl_of_indep hs hcon hcf
      have hlt := card_lt_of_triangleFree_of_indep_lt hk G htf hind
      omega
    · exact Or.inl htf

/-- **NEW — UNCONDITIONAL, and the first upper bound on `R(3,·)` in this campaign.**
`R(3,k) ≤ k²`. Shearer's theorem is the assertion that the right-hand side can be divided by
`(1+o(1))·log k`; Attack01's `conjecture_c_eq_half_iff_upper_of_hhkp` says the `c = 1/2`
conjecture is the assertion that it can be divided by `(2+o(1))·log k`. -/
theorem R_three_le_sq (k : ℕ) : R 3 k ≤ k * k :=
  Nat.sInf_le (isRamseyBound_three_sq k)

/-- **NEW — OBSTRUCTION 4 OF ATTACK01, DISCHARGED.** Attack01 carried
`(RamseySet 3 k).Nonempty` as a hypothesis on five statements because Ramsey's theorem is
absent from Mathlib. For `s = 3` it is now a theorem: `k²` is a member. -/
theorem RamseySet_three_nonempty (k : ℕ) : (RamseySet 3 k).Nonempty :=
  ⟨k * k, isRamseyBound_three_sq k⟩

/-! ### §4a. Attack01's conditional statements, restated with the hypothesis discharged. -/

/-- **NEW — unconditional.** -/
theorem R_three_le_iff {k n : ℕ} : R 3 k ≤ n ↔ IsRamseyBound 3 k n :=
  R_le_iff_of_nonempty (RamseySet_three_nonempty k)

/-- **NEW — unconditional.** -/
theorem lt_R_of_witness_uncond {k n : ℕ} (G : SimpleGraph (Fin n))
    (htri : G.CliqueFree 3) (hind : Gᶜ.CliqueFree k) : n < R 3 k :=
  lt_R_of_witness G htri hind (RamseySet_three_nonempty k)

/-- **NEW — unconditional.** The trivial lower bound. -/
theorem le_R_three (k : ℕ) : k ≤ R 3 k :=
  le_R_of_nonempty (RamseySet_three_nonempty k)

/-- **NEW — unconditional.** `k ≤ R(3,k) ≤ k²`, both sides now theorems. -/
theorem R_three_mem_Icc (k : ℕ) : k ≤ R 3 k ∧ R 3 k ≤ k * k :=
  ⟨le_R_three k, R_three_le_sq k⟩

/-- **NEW — unconditional.** Attack01's `lower_bound_of_witness_family` with its Ramsey
hypothesis removed: the lower-bound literature is now typed as a pure construction problem
with no side conditions at all. -/
theorem lower_bound_of_witness_family_uncond {c : ℝ} (n : ℕ → ℕ)
    (hwit : ∀ k : ℕ, ∃ G : SimpleGraph (Fin (n k)), G.CliqueFree 3 ∧ Gᶜ.CliqueFree k)
    (hsize : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (n k : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (R 3 k : ℝ) := by
  intro ε hε
  filter_upwards [hsize ε hε] with k hk
  obtain ⟨G, htri, hind⟩ := hwit k
  have hlt : n k < R 3 k := lt_R_of_witness_uncond G htri hind
  have hcast : (n k : ℝ) ≤ (R 3 k : ℝ) := by exact_mod_cast hlt.le
  linarith

/-! ### §4b. **NEW — OBSTRUCTION 5 OF ATTACK01, CLOSED: `R(3,3) = 6` exactly.**

Attack01 recorded `R(3,3) ≤ 6` as "not attempted", noting that `decide` is unavailable
(`CliqueFree` carries no `Decidable` instance and `2^15` graphs is out of kernel range anyway).
The neighbourhood machinery of §3 does it with no search at all: if neither `G` nor `Gᶜ` has a
triangle, then by `indep_neighborhood` each of the two neighbourhoods of a fixed vertex is an
independent set of the other graph, so each has at most `2` elements — but together they
partition the other `5` vertices. -/

theorem isRamseyBound_three_three_six : IsRamseyBound 3 3 6 := by
  intro G
  by_cases hG : G.CliqueFree 3
  · by_cases hGc : Gᶜ.CliqueFree 3
    · exfalso
      classical
      obtain ⟨N, hN⟩ : ∃ N : Fin 6 → Finset (Fin 6), ∀ v w, w ∈ N v ↔ G.Adj v w :=
        ⟨fun v => Finset.univ.filter (fun w => G.Adj v w), by intro v w; simp⟩
      obtain ⟨M, hM⟩ : ∃ M : Fin 6 → Finset (Fin 6), ∀ v w, w ∈ M v ↔ Gᶜ.Adj v w :=
        ⟨fun v => Finset.univ.filter (fun w => Gᶜ.Adj v w), by intro v w; simp⟩
      have hv0 : (0 : Fin 6) ∈ (Finset.univ : Finset (Fin 6)) := Finset.mem_univ _
      -- the two neighbourhoods of vertex `0` are independent in the OPPOSITE graph
      have hNi : IsIndep G (N 0) := indep_neighborhood hG hN 0
      have hMi : IsIndep Gᶜ (M 0) := indep_neighborhood hGc hM 0
      have hcard1 : (N 0).card < 3 := by
        by_contra hc
        push_neg at hc
        exact not_cliqueFree_compl_of_indep hNi hc hGc
      have hcard2 : (M 0).card < 3 := by
        by_contra hc
        push_neg at hc
        have hno := not_cliqueFree_compl_of_indep hMi hc
        rw [compl_compl] at hno
        exact hno hG
      -- but they partition the remaining five vertices
      have hdisj : Disjoint (N 0) (M 0) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        have h1 := (hN 0 a).mp ha
        have h2 := (hM 0 a).mp hb
        rw [SimpleGraph.compl_adj] at h2
        exact h2.2 h1
      have hunion : N 0 ∪ M 0 = (Finset.univ : Finset (Fin 6)).erase 0 := by
        ext a
        constructor
        · intro ha
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ a⟩
          rcases Finset.mem_union.mp ha with h | h
          · exact ((hN 0 a).mp h).ne'
          · exact ((hM 0 a).mp h).ne'
        · intro ha
          have hav : a ≠ 0 := (Finset.mem_erase.mp ha).1
          by_cases hadj : G.Adj 0 a
          · exact Finset.mem_union_left _ ((hN 0 a).mpr hadj)
          · refine Finset.mem_union_right _ ((hM 0 a).mpr ?_)
            rw [SimpleGraph.compl_adj]
            exact ⟨fun h => hav h.symm, hadj⟩
      have hsum : (N 0).card + (M 0).card = 5 := by
        have h1 : (N 0 ∪ M 0).card = (N 0).card + (M 0).card :=
          Finset.card_union_of_disjoint hdisj
        have h2 : ((Finset.univ : Finset (Fin 6)).erase 0).card
            = (Finset.univ : Finset (Fin 6)).card - 1 := Finset.card_erase_of_mem hv0
        have h3 : (Finset.univ : Finset (Fin 6)).card = 6 := Finset.card_fin 6
        rw [hunion] at h1
        omega
      omega
    · exact Or.inr hGc
  · exact Or.inl hG

/-- **NEW — unconditional, and a third exact value of the very function this problem is about.**
`R(3,3) = 6`. Attack01 proved `R(3,1) = 1` (spec) and `R(3,2) = 3`; the lower half `6 ≤ R(3,3)`
was conditional on Ramsey's theorem and the upper half was not attempted. Both are now closed. -/
theorem R_three_three_eq_six : R 3 3 = 6 := by
  have hle : R 3 3 ≤ 6 := Nat.sInf_le isRamseyBound_three_three_six
  have hge : 6 ≤ R 3 3 := six_le_R_three_three (RamseySet_three_nonempty 3)
  omega

/-! ### §4c. The sealed bound at the literature's scale. -/

/-- **NEW — unconditional.** `R(3,k) ≤ k²` written against `scale k = k²/log k`: the trivial
bound is exactly a factor `log k` away from Shearer's. That factor is the entire subject of
OBSTRUCTION 2. -/
theorem R_le_log_mul_scale {k : ℕ} (hk : 2 ≤ k) : (R 3 k : ℝ) ≤ Real.log k * scale k := by
  have h1 : (R 3 k : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast R_three_le_sq k
  have h2 : Real.log k * scale k = (k : ℝ) ^ 2 := by
    rw [mul_comm]
    exact scale_mul_log hk
  rw [h2]
  calc (R 3 k : ℝ) ≤ ((k * k : ℕ) : ℝ) := h1
    _ = (k : ℝ) ^ 2 := by push_cast; ring

/-- **NEW — unconditional.** The same statement as a bound on the spec's ratio. It is finite for
each `k` but unbounded in `k`, which is precisely why the trivial argument says nothing about
the Erdős constant and Shearer's is needed. -/
theorem ratio_le_log {k : ℕ} (hk : 2 ≤ k) :
    (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 ≤ Real.log k :=
  ratio_le_of_scale_le hk (R_le_log_mul_scale hk)

/-! ## §5. **NEW** — the function analysis of Shearer's `f`.

`f(x) = (x·log x − x + 1)/(x−1)²` is the independence-ratio function of Shearer (1983).
Everything in this section is proved; none of it depends on Shearer's theorem. -/

/-- **NEW.** Shearer's function. -/
noncomputable def shearerF (x : ℝ) : ℝ := (x * Real.log x - x + 1) / (x - 1) ^ 2

/-- **NEW — the upper half of the sandwich.** `f(x) < log x/(x−1)`, from `log x < x − 1`. -/
theorem shearerF_lt {x : ℝ} (hx1 : 1 < x) : shearerF x < Real.log x / (x - 1) := by
  have hx : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hd : (0 : ℝ) < x - 1 := by linarith
  have hsq : (0 : ℝ) < (x - 1) ^ 2 := by positivity
  have hlog : Real.log x < x - 1 := Real.log_lt_sub_one_of_pos hx hx1.ne'
  rw [shearerF, div_lt_iff₀ hsq]
  have heq : Real.log x / (x - 1) * (x - 1) ^ 2 = Real.log x * (x - 1) := by
    field_simp
  rw [heq]
  nlinarith [mul_pos hd (sub_pos.mpr hlog)]

/-- **NEW — the lower half of the sandwich.** `(log x − 1)/(x−1) < f(x)`, from `log x > 0`. -/
theorem lt_shearerF {x : ℝ} (hx1 : 1 < x) : (Real.log x - 1) / (x - 1) < shearerF x := by
  have hd : (0 : ℝ) < x - 1 := by linarith
  have hsq : (0 : ℝ) < (x - 1) ^ 2 := by positivity
  have hpos : 0 < Real.log x := Real.log_pos hx1
  rw [shearerF, lt_div_iff₀ hsq]
  have heq : (Real.log x - 1) / (x - 1) * (x - 1) ^ 2 = (Real.log x - 1) * (x - 1) := by
    field_simp
  rw [heq]
  nlinarith [mul_pos hd hpos]

/-- **NEW.** The sandwich in one statement: `f(x)` is pinned between two explicit elementary
functions, both asymptotic to `log x / x`. This is the sense in which Shearer's input is
`log D / D` where Caro–Wei's is `1/(D+1)`. -/
theorem shearerF_sandwich {x : ℝ} (hx1 : 1 < x) :
    (Real.log x - 1) / (x - 1) < shearerF x ∧ shearerF x < Real.log x / (x - 1) :=
  ⟨lt_shearerF hx1, shearerF_lt hx1⟩

/-- **NEW.** `1 < exp 1`. -/
theorem one_lt_exp_one : (1 : ℝ) < Real.exp 1 := by
  have h0 : Real.exp 0 < Real.exp 1 := Real.exp_lt_exp.mpr zero_lt_one
  rwa [Real.exp_zero] at h0

/-- **NEW.** `f` is positive beyond `e`. -/
theorem shearerF_pos {x : ℝ} (hx : Real.exp 1 < x) : 0 < shearerF x := by
  have hx1 : (1 : ℝ) < x := lt_trans one_lt_exp_one hx
  have hlog : 1 < Real.log x := by
    have h := Real.log_lt_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at h
  have hd : (0 : ℝ) < x - 1 := by linarith
  have h2 : 0 < (Real.log x - 1) / (x - 1) := div_pos (by linarith) hd
  have h3 := lt_shearerF hx1
  linarith

/-- **NEW — THE POINT OF SHEARER'S FUNCTION, PROVED.** Beyond `x = e²`, Shearer's independence
input `f(x)` is STRICTLY LARGER than the Caro–Wei input `1/(x+1)` used in §4. Since §4 turned
`1/(x+1)` into `R(3,k) ≤ k²`, this inequality is the exact formal sense in which Shearer's
theorem improves the bound — and it is the only part of that improvement provable without
Shearer's inequality itself. -/
theorem carowei_lt_shearerF {x : ℝ} (hx : Real.exp 2 < x) : 1 / (x + 1) < shearerF x := by
  have hexp : (1 : ℝ) < Real.exp 2 := by
    have h0 : Real.exp 0 < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
    rwa [Real.exp_zero] at h0
  have hx1 : (1 : ℝ) < x := lt_trans hexp hx
  have hlog : 2 < Real.log x := by
    have h := Real.log_lt_log (Real.exp_pos 2) hx
    rwa [Real.log_exp] at h
  have hd : (0 : ℝ) < x - 1 := by linarith
  have hd' : (0 : ℝ) < x + 1 := by linarith
  have step12 : 1 / (x + 1) < (Real.log x - 1) / (x - 1) := by
    rw [div_lt_div_iff₀ hd' hd]
    nlinarith [mul_pos (show (0 : ℝ) < Real.log x - 2 by linarith) hd']
  have step3 := lt_shearerF hx1
  linarith

/-! ## §6. **NEW** — OBSTRUCTION 2, SPLIT IN TWO.

Attack01 carried Shearer's ASYMPTOTIC Ramsey bound as one opaque hypothesis. Here it is
decomposed into a finite combinatorial inequality (`ShearerBound`, the published theorem) and an
elementary calculus estimate about `f` alone (`hest`), with the deduction between them PROVED.
That is the sharpening: what remains unformalized is now a single 1983 inequality plus an
undergraduate limit computation, not a Ramsey asymptotic. -/

/-- **NEW — SHEARER'S INEQUALITY (1983), max-degree form. CARRIED AS A HYPOTHESIS, NOT PROVED.**
Every triangle-free graph on `n` vertices whose neighbourhoods have at most `D` elements
contains an independent set of size at least `n·f(D)`. (Shearer states this with the AVERAGE
degree; the max-degree form follows because `f` is decreasing. Neither is proved here.)

The `D ∈ {0,1}` junk of `f` is harmless: `f(1)` is `0/0 = 0` in Lean, so the statement is
vacuously weak there rather than false. -/
def ShearerBound : Prop :=
  ∀ (n D : ℕ) (G : SimpleGraph (Fin n)) (N : Fin n → Finset (Fin n)),
    G.CliqueFree 3 → (∀ v w, w ∈ N v ↔ G.Adj v w) → (∀ v, (N v).card ≤ D) →
    ∃ s : Finset (Fin n), IsIndep G s ∧ (n : ℝ) * shearerF (D : ℝ) ≤ (s.card : ℝ)

/-- **NEW — the same dichotomy of §4, run with Shearer's input instead of Caro–Wei's.**
Granting `ShearerBound`, a vertex count `n` with `n·f(k−1) ≥ k` is a Ramsey upper bound.
Compare `card_lt_of_triangleFree_of_indep_lt`, which is this statement at `f = 1/(D+1)` and is
proved outright. -/
theorem R_three_le_of_shearerBound (hS : ShearerBound) {k n : ℕ} (hk : 1 ≤ k)
    (hn : (k : ℝ) ≤ (n : ℝ) * shearerF ((k : ℝ) - 1)) : R 3 k ≤ n := by
  refine Nat.sInf_le ?_
  intro G
  by_cases htf : G.CliqueFree 3
  · refine Or.inr ?_
    intro hcf
    classical
    obtain ⟨N, hN⟩ : ∃ N : Fin n → Finset (Fin n), ∀ v w, w ∈ N v ↔ G.Adj v w :=
      ⟨fun v => Finset.univ.filter (fun w => G.Adj v w), by intro v w; simp⟩
    have hind : ∀ s : Finset (Fin n), IsIndep G s → s.card < k := by
      intro s hs
      by_contra hcon
      push_neg at hcon
      exact not_cliqueFree_compl_of_indep hs hcon hcf
    have hNcard : ∀ v, (N v).card ≤ k - 1 := by
      intro v
      have hlt := hind _ (indep_neighborhood htf hN v)
      omega
    obtain ⟨s, hsi, hsc⟩ := hS n (k - 1) G N htf hN hNcard
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk, Nat.cast_one]
    rw [hcast] at hsc
    have hks : (k : ℝ) ≤ (s.card : ℝ) := le_trans hn hsc
    have hks' : k ≤ s.card := by exact_mod_cast hks
    have := hind s hsi
    omega
  · exact Or.inl htf

/-- **NEW — THE SPLIT, PROVED.** Shearer's finite inequality plus the elementary estimate
`hest` (for every `ε > 0`, eventually there is an integer `n` with `k ≤ n·f(k−1)` and
`n ≤ (1+ε)·k²/log k`) give exactly the asymptotic upper bound that Attack01 had to assume
wholesale. `hest` mentions neither graphs nor `R`: it is a statement about `f` and `log`. -/
theorem shearer_upper_of_bound_and_estimate (hS : ShearerBound)
    (hest : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∃ n : ℕ, (k : ℝ) ≤ (n : ℝ) * shearerF ((k : ℝ) - 1) ∧ (n : ℝ) ≤ (1 + ε) * scale k) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (1 + ε) * scale k := by
  intro ε hε
  filter_upwards [hest ε hε, eventually_ge_atTop 1] with k hk hk1
  obtain ⟨n, h1, h2⟩ := hk
  have hR : R 3 k ≤ n := R_three_le_of_shearerBound hS hk1 h1
  have hcast : (R 3 k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hR
  linarith

/-- **NEW — the campaign's window, rebuilt on the split.** Attack01's
`question_constant_mem_Icc_of_bounds` pinned the Erdős constant to `[1/2, 1]` from two opaque
literature hypotheses. Here the upper one is replaced by `ShearerBound + hest`, so the window
now rests on: one 1983 combinatorial inequality, one elementary limit computation, and the HHKP
lower bound. Nothing else. -/
theorem question_constant_mem_Icc_of_shearer (hS : ShearerBound)
    (hest : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∃ n : ℕ, (k : ℝ) ≤ (n : ℝ) * shearerF ((k : ℝ) - 1) ∧ (n : ℝ) ≤ (1 + ε) * scale k)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 2 - ε) * scale k ≤ (R 3 k : ℝ)) :
    Question →
      ∃ c : ℝ, (1 : ℝ) / 2 ≤ c ∧ c ≤ 1 ∧
        Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  exact ⟨c, limit_ge_of_lower_bound hlow hc,
    limit_le_of_upper_bound (shearer_upper_of_bound_and_estimate hS hest) hc, hc⟩

/-- **NEW.** And the same for TARGET 3: granting HHKP, `c = 1/2` is equivalent to Shearer's
constant being improvable to `1/2`. Stated here against the SPLIT hypotheses so the residue is
visible: `ShearerBound` at input `f` gives `1`; the conjecture needs an input twice as large. -/
theorem conjecture_c_eq_half_needs_better_input
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 2 - ε) * scale k ≤ (R 3 k : ℝ))
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ ((1 : ℝ) / 2 + ε) * scale k) :
    Conjecture_c_eq_half := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hε : 0 < ((1 : ℝ) / 2 - a) / 2 := by linarith
    filter_upwards [hlow (((1 : ℝ) / 2 - a) / 2) hε, eventually_ge_atTop 2] with k h1 h2
    have := le_ratio_of_le_scale h2 h1
    linarith
  · intro a ha
    have hε : 0 < (a - (1 : ℝ) / 2) / 2 := by linarith
    filter_upwards [hup ((a - (1 : ℝ) / 2) / 2) hε, eventually_ge_atTop 2] with k h1 h2
    have := ratio_le_of_scale_le h2 h1
    linarith

/-! ## §7. **NEW** — the elementary half of the split, PROVED. `hest` is not a hypothesis.

Everything here is about `shearerF` and `Real.log`; no graph and no Ramsey number appears until
the final two theorems. The consequence is that `ShearerBound` — Shearer's finite independence
inequality — is the ONLY unformalized input left in the constant-`1` upper bound. -/

/-- **NEW.** `log k → ∞`, in the only form needed: for any bound `B`, eventually `log k ≥ B`.
Proved from monotonicity of `log` at `exp B`, so no limit-composition API is used. -/
theorem eventually_log_ge (B : ℝ) : ∀ᶠ k : ℕ in atTop, B ≤ Real.log k := by
  filter_upwards [eventually_ge_atTop (⌈Real.exp B⌉₊ + 1)] with k hk
  have h1 : ((⌈Real.exp B⌉₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have h2 : Real.exp B ≤ ((⌈Real.exp B⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h3 : Real.exp B < (k : ℝ) := by linarith
  have h4 := Real.log_lt_log (Real.exp_pos B) h3
  rw [Real.log_exp] at h4
  exact h4.le

/-- **NEW.** `k²/log k ≥ k`, because `log k ≤ k − 1`. This is all the divergence of `scale`
that the estimate needs. -/
theorem scale_ge_self {k : ℕ} (hk : 2 ≤ k) : (k : ℝ) ≤ scale k := by
  have hL : 0 < Real.log k := log_nat_pos hk
  have hk0' : (0 : ℕ) < k := by omega
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0'
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (k : ℝ) ≠ 1 := by linarith
  have hlt : Real.log k < (k : ℝ) - 1 := Real.log_lt_sub_one_of_pos hk0 hk1
  rw [scale, le_div_iff₀ hL]
  nlinarith [mul_lt_mul_of_pos_left hlt hk0, hk0]

/-- **NEW — THE ELEMENTARY HALF OF SHEARER'S ESTIMATE, PROVED.**
For every `ε > 0`, eventually there is an integer `n` with `k ≤ n·f(k−1)` and
`n ≤ (1+ε)·k²/log k`. The witness is `n = ⌈k/f(k−1)⌉`; the two facts driving it are the §5
sandwich `f(x) > (log x − 1)/(x−1)` and `log(k−1) ≥ log k − log 2`. -/
theorem shearer_estimate (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∃ n : ℕ,
      (k : ℝ) ≤ (n : ℝ) * shearerF ((k : ℝ) - 1) ∧ (n : ℝ) ≤ (1 + ε) * scale k := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hεhalf : (0 : ℝ) ≤ ε / 2 := by linarith
  have hmul : (ε / 2) * ((1 + ε / 2) * (Real.log 2 + 1) * (2 / ε))
      = (1 + ε / 2) * (Real.log 2 + 1) := by
    first
      | (field_simp; ring)
      | field_simp
  filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop (⌈2 / ε⌉₊ + 1),
      eventually_log_ge ((1 + ε / 2) * (Real.log 2 + 1) * (2 / ε)),
      eventually_log_ge (Real.log 2 + 2)] with k hk3 hkN hLa hLb
  have hk2 : 2 ≤ k := by omega
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hL : 0 < Real.log k := log_nat_pos hk2
  have hS : 0 < scale k := scale_pos hk2
  have hSk : (k : ℝ) ≤ scale k := scale_ge_self hk2
  have hx1 : (1 : ℝ) < (k : ℝ) - 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : Real.log k - Real.log 2 ≤ Real.log ((k : ℝ) - 1) := by
    have hhalf : (k : ℝ) / 2 < (k : ℝ) - 1 := by linarith
    have hpos : (0 : ℝ) < (k : ℝ) / 2 := by linarith
    have h := Real.log_lt_log hpos hhalf
    rw [Real.log_div (ne_of_gt hk0) (by norm_num)] at h
    linarith
  have hk2pos : (0 : ℝ) < (k : ℝ) - 1 - 1 := by linarith
  have hfm : Real.log ((k : ℝ) - 1) - 1 < shearerF ((k : ℝ) - 1) * ((k : ℝ) - 1 - 1) :=
    (div_lt_iff₀ hk2pos).mp (lt_shearerF hx1)
  have hA : (0 : ℝ) < Real.log k - Real.log 2 - 1 := by linarith
  have hF : 0 < shearerF ((k : ℝ) - 1) := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (neg_nonneg.mpr hcon) hk2pos.le]
  have hkA : Real.log k - Real.log 2 - 1 ≤ (k : ℝ) * shearerF ((k : ℝ) - 1) := by
    nlinarith [hF, hfm, hlogx]
  have h1 : (ε / 2) * ((1 + ε / 2) * (Real.log 2 + 1) * (2 / ε)) ≤ (ε / 2) * Real.log k :=
    mul_le_mul_of_nonneg_left hLa hεhalf
  rw [hmul] at h1
  have key : Real.log k ≤ (1 + ε / 2) * (Real.log k - Real.log 2 - 1) := by nlinarith [h1]
  have hSL : Real.log k * scale k = (k : ℝ) ^ 2 := by
    rw [mul_comm]
    exact scale_mul_log hk2
  have hstepA : (k : ℝ) / shearerF ((k : ℝ) - 1) ≤ (1 + ε / 2) * scale k := by
    rw [div_le_iff₀ hF]
    have e1 : (Real.log k - Real.log 2 - 1) * scale k
        ≤ ((k : ℝ) * shearerF ((k : ℝ) - 1)) * scale k :=
      mul_le_mul_of_nonneg_right hkA hS.le
    have e1' : (1 + ε / 2) * ((Real.log k - Real.log 2 - 1) * scale k)
        ≤ (1 + ε / 2) * (((k : ℝ) * shearerF ((k : ℝ) - 1)) * scale k) :=
      mul_le_mul_of_nonneg_left e1 (by linarith)
    have e2 : Real.log k * scale k
        ≤ ((1 + ε / 2) * (Real.log k - Real.log 2 - 1)) * scale k :=
      mul_le_mul_of_nonneg_right key hS.le
    have e3 : (k : ℝ) ^ 2
        ≤ (1 + ε / 2) * ((k : ℝ) * shearerF ((k : ℝ) - 1) * scale k) := by
      nlinarith [e1', e2, hSL]
    nlinarith [e3, hk0, mul_pos hk0 hk0]
  have hstepB : (1 : ℝ) ≤ (ε / 2) * scale k := by
    have hc1 : (2 / ε) ≤ ((⌈2 / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hc2 : ((⌈2 / ε⌉₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hkN
    have hc3 : (2 / ε) ≤ scale k := by linarith
    have hc4 : (ε / 2) * (2 / ε) ≤ (ε / 2) * scale k := mul_le_mul_of_nonneg_left hc3 hεhalf
    have hc5 : (ε / 2) * (2 / ε) = 1 := by
      first
        | (field_simp; ring)
        | field_simp
    linarith
  refine ⟨⌈(k : ℝ) / shearerF ((k : ℝ) - 1)⌉₊, ?_, ?_⟩
  · have hle : (k : ℝ) / shearerF ((k : ℝ) - 1)
        ≤ ((⌈(k : ℝ) / shearerF ((k : ℝ) - 1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    exact (div_le_iff₀ hF).mp hle
  · have hnn : (0 : ℝ) ≤ (k : ℝ) / shearerF ((k : ℝ) - 1) := le_of_lt (div_pos hk0 hF)
    have hceil : ((⌈(k : ℝ) / shearerF ((k : ℝ) - 1)⌉₊ : ℕ) : ℝ)
        < (k : ℝ) / shearerF ((k : ℝ) - 1) + 1 := Nat.ceil_lt_add_one hnn
    linarith

/-- **NEW — THE RESIDUE OF OBSTRUCTION 2, NAMED EXACTLY.** Shearer's FINITE independence
inequality alone gives his asymptotic Ramsey bound `R(3,k) ≤ (1+o(1))·k²/log k`. There is no
second hypothesis: the elementary half is `shearer_estimate`, proved above.

So the unformalized content of Shearer's 1983 upper bound is now exactly `ShearerBound`, and
by Attack01's `conjecture_c_eq_half_iff_upper_of_hhkp` the open problem is exactly the question
of whether `ShearerBound` can be run with an independence input twice as large. -/
theorem shearer_upper_of_bound (hS : ShearerBound) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (1 + ε) * scale k :=
  shearer_upper_of_bound_and_estimate hS shearer_estimate

/-- **NEW — the campaign's window on two hypotheses only.** The Erdős constant lies in
`[1/2, 1]` given Shearer's finite inequality and the HHKP lower bound. Attack01 needed the whole
asymptotic upper bound as an assumption; that assumption is now derived. -/
theorem question_constant_mem_Icc_of_shearerBound (hS : ShearerBound)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 2 - ε) * scale k ≤ (R 3 k : ℝ)) :
    Question →
      ∃ c : ℝ, (1 : ℝ) / 2 ≤ c ∧ c ≤ 1 ∧
        Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  exact ⟨c, limit_ge_of_lower_bound hlow hc,
    limit_le_of_upper_bound (shearer_upper_of_bound hS) hc, hc⟩

end Erdos165

-- ⛔ FOOTPRINTS. Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` would mean the
-- line is NOT proved. This file contains no `sorry`.
#print axioms Erdos165.IsIndep
#print axioms Erdos165.isIndep_iff_compl_isClique
#print axioms Erdos165.IsIndep.subset
#print axioms Erdos165.not_cliqueFree_compl_of_indep
#print axioms Erdos165.three_clique_of_adj
#print axioms Erdos165.indep_neighborhood
#print axioms Erdos165.exists_indep_of_cover
#print axioms Erdos165.card_lt_of_triangleFree_of_indep_lt
#print axioms Erdos165.R_three_le_of_indep_guarantee
#print axioms Erdos165.isRamseyBound_three_sq
#print axioms Erdos165.R_three_le_sq
#print axioms Erdos165.RamseySet_three_nonempty
#print axioms Erdos165.R_three_le_iff
#print axioms Erdos165.lt_R_of_witness_uncond
#print axioms Erdos165.le_R_three
#print axioms Erdos165.R_three_mem_Icc
#print axioms Erdos165.lower_bound_of_witness_family_uncond
#print axioms Erdos165.isRamseyBound_three_three_six
#print axioms Erdos165.R_three_three_eq_six
#print axioms Erdos165.R_le_log_mul_scale
#print axioms Erdos165.ratio_le_log
#print axioms Erdos165.shearerF_lt
#print axioms Erdos165.lt_shearerF
#print axioms Erdos165.shearerF_sandwich
#print axioms Erdos165.one_lt_exp_one
#print axioms Erdos165.shearerF_pos
#print axioms Erdos165.carowei_lt_shearerF
#print axioms Erdos165.R_three_le_of_shearerBound
#print axioms Erdos165.shearer_upper_of_bound_and_estimate
#print axioms Erdos165.question_constant_mem_Icc_of_shearer
#print axioms Erdos165.conjecture_c_eq_half_needs_better_input
#print axioms Erdos165.eventually_log_ge
#print axioms Erdos165.scale_ge_self
#print axioms Erdos165.shearer_estimate
#print axioms Erdos165.shearer_upper_of_bound
#print axioms Erdos165.question_constant_mem_Icc_of_shearerBound
