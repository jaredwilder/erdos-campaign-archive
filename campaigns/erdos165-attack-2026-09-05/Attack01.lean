/-
# Erdős #165 — ATTACK FILE 01 (2026-09-05)

Target row: `erdos:165` in `oracle/evidence/targets/formalized-open-targets.jsonl`.
Frozen spec: `oracle/evidence/formalizer-sources/erdos/erdos-165.lean` (NOT modified, NOT imported).

⛔ THIS FILE CLOSES NOTHING. `R(3,k) ~ c·k²/log k` is open; the constant is pinned by the
literature only to `[1/2, 1]`. What this file does is (a) prove NEW unconditional facts about
the formalized `R`, and (b) seal the DEDUCTIVE content around the three named targets, with the
cited literature bounds carried as EXPLICIT HYPOTHESES rather than as `sorry`. A hypothesis is
honest; a `sorry` is a fabricated result wearing a theorem's clothes.

Definitions below are copied VERBATIM from the frozen spec.
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

/-- TARGET 2. VERBATIM from the spec. -/
def Conjecture_pgm_quarter_is_truth : Prop :=
  Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 ((1 : ℝ) / 4))

/-- TARGET 3. VERBATIM from the spec. -/
def Conjecture_c_eq_half : Prop :=
  Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 ((1 : ℝ) / 2))

/-! ## §1. NEW unconditional structure of the formalized `R`.
These are proofs about the DEFINITION, and they are what makes the definition falsifiable:
if `R` as written were not the Ramsey number, `R_three_two` below would be the wrong value. -/

/-- **NEW.** No graph is `0`-clique-free: the empty set is a `0`-clique. -/
theorem not_cliqueFree_zero {V : Type*} (G : SimpleGraph V) : ¬ G.CliqueFree 0 := by
  intro h
  exact h ∅ ⟨by simp [SimpleGraph.IsClique], by simp⟩

/-- **NEW.** The forcing condition is vacuous when the blue parameter is `0`. -/
theorem isRamseyBound_zero_right (s n : ℕ) : IsRamseyBound s 0 n :=
  fun _ => Or.inr (not_cliqueFree_zero _)

/-- **NEW.** `R(s,0) = 0` — a junk value of the definition, recorded so it cannot be mistaken
for content. (Convention (4) of the spec says junk values are never read; this pins one.) -/
theorem R_zero_right (s : ℕ) : R s 0 = 0 :=
  Nat.le_zero.mp (Nat.sInf_le (isRamseyBound_zero_right s 0))

/-- **NEW — stated without Mathlib's containment API on purpose.** Clique-freeness pulls back
along an injection: a clique in the pullback maps forward to a clique of the same size.
(Mathlib's `CliqueFree.comap` is phrased through `IsContained`/`Copy`, whose shape has moved
between revisions; this proof uses only `Finset.map` and `Finset.card_map`.) -/
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

/-- **NEW — the key structural fact.** `IsRamseyBound s t ·` is upward closed: adding vertices
never destroys the forcing property. This is what makes `sInf` in the spec's definition of `R`
the right operator, and it is not proved anywhere in the spec. -/
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

/-- **NEW.** `RamseySet s t` is upward closed. -/
theorem RamseySet_upward_closed {s t n m : ℕ} (hnm : n ≤ m) (hn : n ∈ RamseySet s t) :
    m ∈ RamseySet s t :=
  isRamseyBound_mono_n hnm hn

/-- **NEW.** Monotonicity in the RED parameter. The spec proves the `t` (blue) case only. -/
theorem isRamseyBound_mono_left {s s' t n : ℕ} (h : s' ≤ s) (hb : IsRamseyBound s t n) :
    IsRamseyBound s' t n := by
  intro G
  rcases hb G with h1 | h1
  · exact Or.inl fun hf => h1 (hf.mono h)
  · exact Or.inr h1

/-- **NEW.** `R(·, t)` is monotone. Nonemptiness stands in for Ramsey's theorem. -/
theorem R_mono_left {s s' t : ℕ} (h : s' ≤ s) (hne : (RamseySet s t).Nonempty) :
    R s' t ≤ R s t :=
  Nat.sInf_le (isRamseyBound_mono_left h (Nat.sInf_mem hne))

/-- **NEW.** `R` is characterised by upward closure: below `R` nothing forces, at or above it
everything does. Only available because of `isRamseyBound_mono_n`. -/
theorem R_le_iff_of_nonempty {s t n : ℕ} (hne : (RamseySet s t).Nonempty) :
    R s t ≤ n ↔ IsRamseyBound s t n :=
  ⟨fun h => isRamseyBound_mono_n h (Nat.sInf_mem hne), fun h => Nat.sInf_le h⟩

/-- **NEW.** A single counterexample graph on `n` vertices pushes `R` strictly above `n`.
This is the shape of every classical Ramsey lower bound. -/
theorem lt_R_of_not_isRamseyBound {s t n : ℕ} (h : ¬ IsRamseyBound s t n)
    (hne : (RamseySet s t).Nonempty) : n < R s t := by
  by_contra hcon
  push_neg at hcon
  exact h (isRamseyBound_mono_n hcon (Nat.sInf_mem hne))

/-- **NEW — the shape of every Ramsey lower bound.** A triangle-free graph on `n` vertices whose
complement has no `K_k` (equivalently: independence number `< k`) certifies `R(3,k) > n`.
Kim's construction, Bohman–Keevash, PGM, CJMS and HHKP are all instances of this reduction. -/
theorem lt_R_of_witness {k n : ℕ} (G : SimpleGraph (Fin n))
    (htri : G.CliqueFree 3) (hind : Gᶜ.CliqueFree k)
    (hne : (RamseySet 3 k).Nonempty) : n < R 3 k := by
  refine lt_R_of_not_isRamseyBound (fun h => ?_) hne
  rcases h G with h1 | h1
  · exact h1 htri
  · exact h1 hind

/-- **NEW.** Fewer than `k` vertices never force a blue `K_k`: the empty graph is a witness
(no triangle, and its complement is complete but too small). -/
theorem not_mem_RamseySet_of_lt {k n : ℕ} (h : n < k) : n ∉ RamseySet 3 k := by
  intro hn
  rcases hn ⊥ with h1 | h1
  · exact h1 (SimpleGraph.cliqueFree_bot (by norm_num))
  · refine h1 ?_
    rw [compl_bot]
    exact SimpleGraph.cliqueFree_of_card_lt (by simpa using h)

/-- **NEW.** The trivial lower bound `R(3,k) ≥ k`. The nonemptiness hypothesis stands in for
Ramsey's theorem, which Mathlib does not have (spec convention (4)). -/
theorem le_R_of_nonempty {k : ℕ} (hne : (RamseySet 3 k).Nonempty) : k ≤ R 3 k := by
  by_contra hcon
  push_neg at hcon
  exact not_mem_RamseySet_of_lt hcon (Nat.sInf_mem hne)

/-- **NEW.** Three vertices force a triangle or a non-edge. -/
theorem isRamseyBound_three_two_three : IsRamseyBound 3 2 3 := by
  intro G
  by_cases h : Gᶜ.CliqueFree 2
  · refine Or.inl ?_
    rw [SimpleGraph.cliqueFree_two] at h
    have hG : G = ⊤ := by
      have h2 : Gᶜᶜ = (⊥ : SimpleGraph (Fin 3))ᶜ := by rw [h]
      simpa using h2
    subst hG
    intro hcf
    refine hcf Finset.univ ⟨?_, ?_⟩
    · intro x _ y _ hxy
      simpa using hxy
    · simp
  · exact Or.inr h

/-- **NEW.** Two vertices do not: the complete graph on two vertices has no triangle and no
non-edge. -/
theorem not_isRamseyBound_three_two_two : ¬ IsRamseyBound 3 2 2 := by
  intro h
  rcases h ⊤ with h1 | h1
  · exact h1 (SimpleGraph.cliqueFree_of_card_lt (by simp))
  · refine h1 ?_
    rw [compl_top]
    exact SimpleGraph.cliqueFree_bot le_rfl

/-- **NEW — a second exact value of the very function this problem is about.**
`R(3,2) = 3`, computed from the spec's definition. The spec proves only `R(3,1) = 1`. -/
theorem R_three_two : R 3 2 = 3 := by
  have ha : IsRamseyBound 3 2 3 := isRamseyBound_three_two_three
  have hle : R 3 2 ≤ 3 := Nat.sInf_le ha
  have hmem : R 3 2 ∈ RamseySet 3 2 := Nat.sInf_mem ⟨3, ha⟩
  have h2 : R 3 2 ≠ 2 := by
    intro he
    rw [he] at hmem
    exact not_isRamseyBound_three_two_two hmem
  have h1 : ¬ (R 3 2 < 2) := fun hlt => not_mem_RamseySet_of_lt hlt hmem
  omega

/-! ### The classical `R(3,3) ≥ 6`, as a live INSTANCE of `lt_R_of_witness`.
A reduction lemma nobody can instantiate is weak evidence; this fires it on the textbook
witness and reproduces a known value of the very function the problem is about. -/

/-- The 5-cycle on `Fin 5` (arithmetic mod 5) — the classical Ramsey witness: triangle-free,
and self-complementary, so its complement is triangle-free too. -/
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

/-- **NEW.** The 5-cycle has no triangle. (`CliqueFree` carries no `Decidable` instance on this
Mathlib rev, so the three edges of a putative triangle are extracted first and the residual
`125`-case statement over `Fin 5` is what gets decided.) -/
theorem C5_triangleFree : C5.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.2
  have h1 : C5.Adj a b := ht.1 (by simp) (by simp) hab
  have h2 : C5.Adj a c := ht.1 (by simp) (by simp) hac
  have h3 : C5.Adj b c := ht.1 (by simp) (by simp) hbc
  revert hab hac hbc h1 h2 h3
  revert a b c
  decide

/-- **NEW.** The 5-cycle has no independent set of size `3`. -/
theorem C5_compl_cliqueFree_three : C5ᶜ.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.2
  have h1 : C5ᶜ.Adj a b := ht.1 (by simp) (by simp) hab
  have h2 : C5ᶜ.Adj a c := ht.1 (by simp) (by simp) hac
  have h3 : C5ᶜ.Adj b c := ht.1 (by simp) (by simp) hbc
  revert hab hac hbc h1 h2 h3
  revert a b c
  decide

/-- **NEW.** Five vertices do not force a monochromatic triangle. -/
theorem not_isRamseyBound_three_three_five : ¬ IsRamseyBound 3 3 5 := by
  intro h
  rcases h C5 with h1 | h1
  · exact h1 C5_triangleFree
  · exact h1 C5_compl_cliqueFree_three

/-- **NEW — `R(3,3) ≥ 6`**, the textbook value, obtained from the spec's definition through
`lt_R_of_witness`. Nonemptiness stands in for Ramsey's theorem (absent from Mathlib). -/
theorem six_le_R_three_three (hne : (RamseySet 3 3).Nonempty) : 6 ≤ R 3 3 :=
  lt_R_of_witness C5 C5_triangleFree C5_compl_cliqueFree_three hne

/-! ## §2. The scale/ratio bridge.
The literature bounds are printed against `scale k = k²/log k`; the three named targets are
stated against the ratio `R(3,k)·log k / k²`. These lemmas are the exact translation, and they
are where the `k ∈ {0,1}` junk of `Real.log` is quarantined (everything is `2 ≤ k`). -/

theorem log_nat_pos {k : ℕ} (hk : 2 ≤ k) : 0 < Real.log k := by
  have hk1 : (1 : ℕ) < k := hk
  exact Real.log_pos (by exact_mod_cast hk1)

theorem sq_nat_pos {k : ℕ} (hk : 2 ≤ k) : (0 : ℝ) < (k : ℝ) ^ 2 := by
  have hk0 : (0 : ℕ) < k := by omega
  have hk0' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  exact pow_pos hk0' 2

theorem scale_pos {k : ℕ} (hk : 2 ≤ k) : 0 < scale k :=
  div_pos (sq_nat_pos hk) (log_nat_pos hk)

theorem scale_mul_log {k : ℕ} (hk : 2 ≤ k) : scale k * Real.log k = (k : ℝ) ^ 2 := by
  have hL : Real.log k ≠ 0 := ne_of_gt (log_nat_pos hk)
  rw [scale]
  field_simp

/-- `a·scale k ≤ R(3,k)` in the literature's shape becomes `a ≤ ratio k`. -/
theorem le_ratio_of_le_scale {a : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (h : a * scale k ≤ (R 3 k : ℝ)) :
    a ≤ (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 := by
  have hL : 0 < Real.log k := log_nat_pos hk
  have hK : (0 : ℝ) < (k : ℝ) ^ 2 := sq_nat_pos hk
  rw [le_div_iff₀ hK]
  calc a * (k : ℝ) ^ 2 = a * (scale k * Real.log k) := by rw [scale_mul_log hk]
    _ = a * scale k * Real.log k := by ring
    _ ≤ (R 3 k : ℝ) * Real.log k := mul_le_mul_of_nonneg_right h hL.le

/-- `R(3,k) ≤ b·scale k` becomes `ratio k ≤ b`. -/
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

/-- The converse translation. -/
theorem le_scale_of_le_ratio {a : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (h : a ≤ (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) :
    a * scale k ≤ (R 3 k : ℝ) := by
  have hL : Real.log k ≠ 0 := ne_of_gt (log_nat_pos hk)
  have hK : ((k : ℝ) ^ 2) ≠ 0 := ne_of_gt (sq_nat_pos hk)
  have hs : 0 < scale k := scale_pos hk
  calc a * scale k ≤ ((R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) * scale k :=
        mul_le_mul_of_nonneg_right h hs.le
    _ = (R 3 k : ℝ) := by rw [scale]; field_simp

/-- The converse translation, upper side. -/
theorem scale_le_of_ratio_le {b : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (h : (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 ≤ b) :
    (R 3 k : ℝ) ≤ b * scale k := by
  have hL : Real.log k ≠ 0 := ne_of_gt (log_nat_pos hk)
  have hK : ((k : ℝ) ^ 2) ≠ 0 := ne_of_gt (sq_nat_pos hk)
  have hs : 0 < scale k := scale_pos hk
  calc (R 3 k : ℝ) = ((R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) * scale k := by
        rw [scale]; field_simp
    _ ≤ b * scale k := mul_le_mul_of_nonneg_right h hs.le

/-! ## §3. Limit constraints — the typed obstruction map.
Every literature bound is carried as an EXPLICIT HYPOTHESIS of exactly the shape the spec
states it in. Nothing here asserts any of those bounds. -/

/-- **NEW.** An eventual lower bound of the literature's shape forces any limit of the ratio to
be at least the constant. -/
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

/-- **NEW.** Dually for an eventual upper bound. -/
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

/-- **NEW.** A lower bound strictly above `c` refutes convergence to `c`. -/
theorem not_tendsto_of_lower_bound {c₀ c : ℝ} (hlt : c < c₀)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c₀ - ε) * scale k ≤ (R 3 k : ℝ)) :
    ¬ Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  intro hc
  have := limit_ge_of_lower_bound hlow hc
  linarith

/-- **NEW.** The published lower constants form a chain: a bound at `c₀` implies the bound at
every `c₁ ≤ c₀`. So Kim `1/162` ⇐ Bohman–Keevash/PGM `1/4` ⇐ CJMS `1/3` ⇐ HHKP `1/2` are
nested, not independent claims. -/
theorem lower_bound_mono {c₀ c₁ : ℝ} (h : c₁ ≤ c₀)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c₀ - ε) * scale k ≤ (R 3 k : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c₁ - ε) * scale k ≤ (R 3 k : ℝ) := by
  intro ε hε
  filter_upwards [hlow ε hε, eventually_ge_atTop 2] with k h1 h2
  have hs : 0 < scale k := scale_pos h2
  linarith [mul_le_mul_of_nonneg_right h hs.le]

/-- **NEW — the lower-bound half of Erdős #165, reduced to pure combinatorics.**
If a family of triangle-free graphs on `n k` vertices with independence number `< k` exists, and
`n k` is eventually at least `(c - ε)·k²/log k`, then the constant `c` is a valid lower constant
for `R(3,k)`. This types the ENTIRE lower-bound literature (Kim `1/162` → HHKP `1/2`) as one
construction problem: build bigger triangle-free graphs with small independence number.
Ramsey's theorem — absent from Mathlib — is carried as the explicit `hne` hypothesis. -/
theorem lower_bound_of_witness_family {c : ℝ} (n : ℕ → ℕ)
    (hwit : ∀ k : ℕ, ∃ G : SimpleGraph (Fin (n k)), G.CliqueFree 3 ∧ Gᶜ.CliqueFree k)
    (hne : ∀ k : ℕ, (RamseySet 3 k).Nonempty)
    (hsize : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (n k : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (R 3 k : ℝ) := by
  intro ε hε
  filter_upwards [hsize ε hε] with k hk
  obtain ⟨G, htri, hind⟩ := hwit k
  have hlt : n k < R 3 k := lt_R_of_witness G htri hind (hne k)
  have hcast : (n k : ℝ) ≤ (R 3 k : ℝ) := by exact_mod_cast hlt.le
  linarith

/-! ### §3a. TARGET 2 (`Conjecture_pgm_quarter_is_truth`) — conditional REFUTATIONS.
The acceptance contract accepts the NEGATION of a target. These reduce that negation to one
cited paper, with nothing else outstanding. -/

/-- **NEW — conditional refutation of TARGET 2 from Campos–Jenssen–Michelen–Sahasrabudhe (2025).**
Their `c ≥ 1/3` bound, in exactly the spec's shape, refutes `c = 1/4`. -/
theorem not_conjecture_pgm_of_cjms
    (hcjms : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 3 - ε) * scale k ≤ (R 3 k : ℝ)) :
    ¬ Conjecture_pgm_quarter_is_truth :=
  not_tendsto_of_lower_bound (by norm_num) hcjms

/-- **NEW — conditional refutation of TARGET 2 from Hefty–Horn–King–Pfender (2025).** -/
theorem not_conjecture_pgm_of_hhkp
    (hhhkp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 2 - ε) * scale k ≤ (R 3 k : ℝ)) :
    ¬ Conjecture_pgm_quarter_is_truth :=
  not_tendsto_of_lower_bound (by norm_num) hhhkp

/-- **NEW — UNCONDITIONAL.** The two recorded conjectures cannot both hold. No literature input
at all: limits in `ℝ` are unique and `1/4 ≠ 1/2`. -/
theorem conjecture_pgm_and_half_incompatible :
    ¬ (Conjecture_pgm_quarter_is_truth ∧ Conjecture_c_eq_half) := by
  rintro ⟨h1, h2⟩
  have h := tendsto_nhds_unique h1 h2
  norm_num at h

/-- **NEW — UNCONDITIONAL.** The spec proves `Conjecture_c_eq_half → Question`; this is the
missing companion for the other conjecture. -/
theorem conjecture_pgm_implies_question : Conjecture_pgm_quarter_is_truth → Question :=
  fun h => ⟨(1 : ℝ) / 4, h⟩

/-! ### §3b. TARGET 1 (`Question`) — the deductive content of the spec's sorried theorem. -/

/-- **NEW — the spec's `question_constant_mem_Icc`, PROVED**, with its two literature inputs
(Hefty–Horn–King–Pfender `c ≥ 1/2`, Shearer `≤ 1 + o(1)`) as explicit hypotheses instead of
`sorry`. The interval `[1/2, 1]` is the width of the open problem; this shows that width is a
pure consequence of the two cited bounds and nothing else. -/
theorem question_constant_mem_Icc_of_bounds
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 2 - ε) * scale k ≤ (R 3 k : ℝ))
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (1 + ε) * scale k) :
    Question →
      ∃ c : ℝ, (1 : ℝ) / 2 ≤ c ∧ c ≤ 1 ∧
        Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  exact ⟨c, limit_ge_of_lower_bound hlow hc, limit_le_of_upper_bound hup hc, hc⟩

/-- **NEW — the spec's `kim_shearer_bounds`, PROVED** from its two named halves. The sandwich
the source calls "known" adds nothing to Kim's lower bound plus Shearer's upper bound. -/
theorem kim_shearer_bounds_of_parts
    (hlow : ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (R 3 k : ℝ))
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (1 + ε) * scale k) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      (c - ε) * scale k ≤ (R 3 k : ℝ) ∧ (R 3 k : ℝ) ≤ (1 + ε) * scale k := by
  obtain ⟨c, hc, hlow⟩ := hlow
  refine ⟨c, hc, fun ε hε => ?_⟩
  filter_upwards [hlow ε hε, hup ε hε] with k h1 h2
  exact ⟨h1, h2⟩

/-- **NEW — the spec's `order_of_magnitude`, PROVED** from the sandwich. `R(3,k) = Θ(k²/log k)`
is a formal consequence of the `o(1)` sandwich, with the constants produced explicitly
(`a = c/2`, `b = 1 + c/2`). This is what is actually settled, as opposed to `Question`. -/
theorem order_of_magnitude_of_kim_shearer
    (h : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      (c - ε) * scale k ≤ (R 3 k : ℝ) ∧ (R 3 k : ℝ) ≤ (1 + ε) * scale k) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ᶠ k : ℕ in atTop, a * scale k ≤ (R 3 k : ℝ) ∧ (R 3 k : ℝ) ≤ b * scale k := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c / 2, 1 + c / 2, by linarith, by linarith, ?_⟩
  filter_upwards [h (c / 2) (by linarith)] with k hk
  have e : c - c / 2 = c / 2 := by ring
  rw [e] at hk
  exact hk

/-- **NEW.** A matching two-sided `ε`-sandwich at a single constant `c` produces the limit.
This is the exact shape any future CLOSE of `Question` must take. -/
theorem tendsto_of_two_sided_bounds {c : ℝ}
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (R 3 k : ℝ))
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (c + ε) * scale k) :
    Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hε : 0 < (c - a) / 2 := by linarith
    filter_upwards [hlow ((c - a) / 2) hε, eventually_ge_atTop 2] with k h1 h2
    show a < (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2
    have := le_ratio_of_le_scale h2 h1
    linarith
  · intro a ha
    have hε : 0 < (a - c) / 2 := by linarith
    filter_upwards [hup ((a - c) / 2) hε, eventually_ge_atTop 2] with k h1 h2
    show (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 < a
    have := ratio_le_of_scale_le h2 h1
    linarith

/-- **NEW.** Consequence: a two-sided sandwich answers TARGET 1. -/
theorem question_of_two_sided_bounds {c : ℝ}
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (R 3 k : ℝ))
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (c + ε) * scale k) :
    Question :=
  ⟨c, tendsto_of_two_sided_bounds hlow hup⟩

/-- **NEW — UNCONDITIONAL, and the sharpest statement in this file.**
Convergence of the ratio to `c` is EQUIVALENT to the two-sided `ε`-sandwich against
`k²/log k` at that same `c`. So the open problem is exactly the problem of matching the
constants, with no analytic slack hidden anywhere else. -/
theorem tendsto_iff_two_sided_bounds {c : ℝ} :
    Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c) ↔
      ((∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (R 3 k : ℝ)) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (c + ε) * scale k)) := by
  constructor
  · intro hc
    refine ⟨?_, ?_⟩
    · intro ε hε
      have h1 : ∀ᶠ k : ℕ in atTop, c - ε < (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 :=
        (tendsto_order.1 hc).1 (c - ε) (by linarith)
      filter_upwards [h1, eventually_ge_atTop 2] with k hk1 hk2
      exact le_scale_of_le_ratio hk2 hk1.le
    · intro ε hε
      have h1 : ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2 < c + ε :=
        (tendsto_order.1 hc).2 (c + ε) (by linarith)
      filter_upwards [h1, eventually_ge_atTop 2] with k hk1 hk2
      exact scale_le_of_ratio_le hk2 hk1.le
  · rintro ⟨hlow, hup⟩
    exact tendsto_of_two_sided_bounds hlow hup

/-! ### §3c. TARGET 3 (`Conjecture_c_eq_half`) — the residue, named exactly. -/

/-- **NEW — conditional CLOSE of TARGET 3.** A matching `1/2` sandwich proves the conjecture. -/
theorem conjecture_c_eq_half_of_bounds
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 2 - ε) * scale k ≤ (R 3 k : ℝ))
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ ((1 : ℝ) / 2 + ε) * scale k) :
    Conjecture_c_eq_half :=
  tendsto_of_two_sided_bounds hlow hup

/-- **NEW — THE OBSTRUCTION, TYPED.** Granting only the published Hefty–Horn–King–Pfender
lower bound `c ≥ 1/2`, TARGET 3 is EQUIVALENT to the matching upper bound
`R(3,k) ≤ (1/2 + o(1)) k²/log k`. The entire remaining content of the `c = 1/2` conjecture is
therefore the improvement of Shearer's constant from `1` to `1/2`, and nothing else. -/
theorem conjecture_c_eq_half_iff_upper_of_hhkp
    (hhhkp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 2 - ε) * scale k ≤ (R 3 k : ℝ)) :
    Conjecture_c_eq_half ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ ((1 : ℝ) / 2 + ε) * scale k := by
  constructor
  · intro h
    exact (tendsto_iff_two_sided_bounds.1 h).2
  · intro hup
    exact tendsto_of_two_sided_bounds hhhkp hup

/-- **NEW — UNCONDITIONAL.** Same move for TARGET 1. (The first draft carried Shearer's upper
bound as a hypothesis; the kernel reported it unused, so it is gone: the equivalence needs no
literature input at all.) `Question` is exactly the existence of a constant with a matching
two-sided sandwich. -/
theorem question_iff_exists_two_sided_bounds :
    Question ↔
      ∃ c : ℝ, (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (R 3 k : ℝ)) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (c + ε) * scale k) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, tendsto_iff_two_sided_bounds.1 hc⟩
  · rintro ⟨c, hlow, hup'⟩
    exact ⟨c, tendsto_of_two_sided_bounds hlow hup'⟩

end Erdos165

-- ⛔ FOOTPRINTS. Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` would mean the
-- line is NOT proved. This file contains no `sorry`.
#print axioms Erdos165.not_cliqueFree_zero
#print axioms Erdos165.isRamseyBound_zero_right
#print axioms Erdos165.R_zero_right
#print axioms Erdos165.cliqueFree_comap
#print axioms Erdos165.isRamseyBound_mono_n
#print axioms Erdos165.RamseySet_upward_closed
#print axioms Erdos165.isRamseyBound_mono_left
#print axioms Erdos165.R_mono_left
#print axioms Erdos165.R_le_iff_of_nonempty
#print axioms Erdos165.lt_R_of_not_isRamseyBound
#print axioms Erdos165.lt_R_of_witness
#print axioms Erdos165.not_mem_RamseySet_of_lt
#print axioms Erdos165.le_R_of_nonempty
#print axioms Erdos165.isRamseyBound_three_two_three
#print axioms Erdos165.not_isRamseyBound_three_two_two
#print axioms Erdos165.R_three_two
#print axioms Erdos165.C5_triangleFree
#print axioms Erdos165.C5_compl_cliqueFree_three
#print axioms Erdos165.not_isRamseyBound_three_three_five
#print axioms Erdos165.six_le_R_three_three
#print axioms Erdos165.log_nat_pos
#print axioms Erdos165.sq_nat_pos
#print axioms Erdos165.scale_pos
#print axioms Erdos165.scale_mul_log
#print axioms Erdos165.le_ratio_of_le_scale
#print axioms Erdos165.ratio_le_of_scale_le
#print axioms Erdos165.le_scale_of_le_ratio
#print axioms Erdos165.scale_le_of_ratio_le
#print axioms Erdos165.limit_ge_of_lower_bound
#print axioms Erdos165.limit_le_of_upper_bound
#print axioms Erdos165.not_tendsto_of_lower_bound
#print axioms Erdos165.lower_bound_mono
#print axioms Erdos165.lower_bound_of_witness_family
#print axioms Erdos165.not_conjecture_pgm_of_cjms
#print axioms Erdos165.not_conjecture_pgm_of_hhkp
#print axioms Erdos165.conjecture_pgm_and_half_incompatible
#print axioms Erdos165.conjecture_pgm_implies_question
#print axioms Erdos165.question_constant_mem_Icc_of_bounds
#print axioms Erdos165.kim_shearer_bounds_of_parts
#print axioms Erdos165.order_of_magnitude_of_kim_shearer
#print axioms Erdos165.tendsto_of_two_sided_bounds
#print axioms Erdos165.question_of_two_sided_bounds
#print axioms Erdos165.tendsto_iff_two_sided_bounds
#print axioms Erdos165.conjecture_c_eq_half_of_bounds
#print axioms Erdos165.conjecture_c_eq_half_iff_upper_of_hhkp
#print axioms Erdos165.question_iff_exists_two_sided_bounds
