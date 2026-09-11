import Mathlib

/-!
# Erdős #616 — attack 01 (2026-09-05)

Target stub: `oracle/evidence/certified-corpus/erdos-616.lean`
Source     : `oracle/evidence/formalizer-sources/erdos/entry-graph-erdos-616.json`
            (Erdős–Hajnal–Tuza [EHT91], `3/16 r + 7/8 ≤ t ≤ 1/5 r`)

All definitions below are copied VERBATIM from the stub.

## What this file establishes

* `window_nonempty_iff` : the claimed EHT window `[3r/16 + 7/8, r/5]` is NONEMPTY iff `r ≥ 70`.
* `window_refutation`   : hence the `∃ t` half of the stub goal is already FALSE at `r = 3`
                          (pure ℚ arithmetic, no hypergraph theory needed).
* `pair_meet`           : for `r ≥ 3`, `LocalOne` forces `H` to be an intersecting family.
* `triple_common`       : for `r ≥ 3`, ANY THREE edges of `H` share a common vertex.
                          (Helly-type structural reduction; the real content of this file.)
* `good_one_le`         : `Good r t → 1 ≤ t` for `r ≥ 1`.
* `good_three_one`      : `Good 3 1` — for `r = 3` the local condition forces `τ ≤ 1` globally.
* `optimal_three`       : `Optimal 3 1` — the exact answer at `r = 3` is `t = 1`.
* `erdos_616_stub_statement_is_false` : the stub's `sorry`'d goal is REFUTED. Not merely by the
                          empty window: at `r = 3` the optimum genuinely EXISTS and equals `1`,
                          while the claimed lower bound demands `t ≥ 23/16`.
-/

noncomputable section
open scoped BigOperators
open scoped Classical

/-! ## Definitions — VERBATIM from the stub -/

def IsCover {n : ℕ} (H : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∀ e ∈ H, (e ∩ S).Nonempty

def CoverAtMost {n : ℕ} (H : Finset (Finset (Fin n))) (t : ℚ) : Prop :=
  ∃ S : Finset (Fin n), (S.card : ℚ) ≤ t ∧ IsCover H S

def Uniform {r n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = r

def LocalOne {r n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ U : Finset (Fin n), U.card ≤ 3 * r - 3 →
    ∃ S : Finset (Fin n), S.card ≤ 1 ∧
      ∀ e ∈ H, e ⊆ U → (e ∩ S).Nonempty

def Claim (r n : ℕ) (H : Finset (Finset (Fin n))) (t : ℚ) : Prop :=
  Uniform (r := r) H → LocalOne (r := r) H → CoverAtMost H t

def Good (r : ℕ) (t : ℚ) : Prop :=
  ∀ n : ℕ, ∀ H : Finset (Finset (Fin n)), Claim r n H t

def Optimal (r : ℕ) (t : ℚ) : Prop :=
  Good r t ∧ ∀ u : ℚ, Good r u → t ≤ u

/-! ## Part 1 — the claimed EHT window is empty for every `r < 70` -/

theorem window_nonempty_iff (r : ℕ) :
    (∃ t : ℚ, ((3 : ℚ) / 16) * r + 7 / 8 ≤ t ∧ t ≤ ((1 : ℚ) / 5) * r) ↔ 70 ≤ r := by
  constructor
  · rintro ⟨t, h1, h2⟩
    have hchain : ((3 : ℚ) / 16) * r + 7 / 8 ≤ ((1 : ℚ) / 5) * r := le_trans h1 h2
    have h70 : (70 : ℚ) ≤ (r : ℚ) := by linarith
    exact_mod_cast h70
  · intro h
    have h70 : (70 : ℚ) ≤ (r : ℚ) := by exact_mod_cast h
    exact ⟨((1 : ℚ) / 5) * r, by linarith, le_refl _⟩

theorem window_empty_of_lt_seventy (r : ℕ) (hr : r < 70) :
    ¬ ∃ t : ℚ, ((3 : ℚ) / 16) * r + 7 / 8 ≤ t ∧ t ≤ ((1 : ℚ) / 5) * r := by
  intro h
  have := (window_nonempty_iff r).mp h
  omega

/-- The `∃ t` half of the stub goal is already false, at `r = 3`, on arithmetic alone. -/
theorem window_refutation :
    ¬ (∀ r : ℕ, 3 ≤ r →
        ∃ t : ℚ, ((3 : ℚ) / 16) * r + 7 / 8 ≤ t ∧ t ≤ ((1 : ℚ) / 5) * r) := by
  intro h
  exact window_empty_of_lt_seventy 3 (by norm_num) (h 3 (by norm_num))

/-! ## Part 2 — elementary facts about covers -/

theorem meet_singleton_iff {n : ℕ} (f : Finset (Fin n)) (v : Fin n) :
    (f ∩ ({v} : Finset (Fin n))).Nonempty ↔ v ∈ f := by
  constructor
  · rintro ⟨x, hx⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hx
    obtain ⟨hxf, rfl⟩ := hx
    exact hxf
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

theorem good_mono {r : ℕ} {t u : ℚ} (h : Good r t) (htu : t ≤ u) : Good r u := by
  unfold Good Claim CoverAtMost
  intro n H hUni hLoc
  obtain ⟨S, hS, hcov⟩ := h n H hUni hLoc
  exact ⟨S, le_trans hS htu, hcov⟩

/-- Any admissible `t` is at least `1`: the single complete edge is a legal instance. -/
theorem good_one_le {r : ℕ} (hr : 0 < r) {t : ℚ} (h : Good r t) : 1 ≤ t := by
  have hUni : Uniform (r := r) ({(Finset.univ : Finset (Fin r))}) := by
    intro e he
    have hev : e = (Finset.univ : Finset (Fin r)) := by simpa using he
    subst hev
    simp
  have hLoc : LocalOne (r := r) ({(Finset.univ : Finset (Fin r))}) := by
    intro U _
    refine ⟨{(⟨0, hr⟩ : Fin r)}, by simp, ?_⟩
    intro e he _
    have hev : e = (Finset.univ : Finset (Fin r)) := by simpa using he
    subst hev
    exact ⟨(⟨0, hr⟩ : Fin r), by simp⟩
  obtain ⟨S, hcard, hcov⟩ := h r ({(Finset.univ : Finset (Fin r))}) hUni hLoc
  obtain ⟨x, hx⟩ := hcov (Finset.univ : Finset (Fin r)) (by simp)
  rw [Finset.mem_inter] at hx
  have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx.2⟩
  have hq : (1 : ℚ) ≤ (S.card : ℚ) := by exact_mod_cast hpos
  linarith

theorem optimal_unique {r : ℕ} {t u : ℚ} (h1 : Optimal r t) (h2 : Optimal r u) : t = u :=
  le_antisymm (h1.2 u h2.1) (h2.2 t h1.1)

/-! ## Part 3 — the structural core, valid for every `r ≥ 3`

`LocalOne` with window `3r-3` is strong enough to force a Helly-type conclusion:
any two edges meet, and any three edges share a common vertex. -/

/-- For `r ≥ 3`, `LocalOne` forces `H` to be an intersecting family:
two `r`-edges span at most `2r ≤ 3r-3` vertices, so the local transversal hits both. -/
theorem pair_meet {r n : ℕ} (hr : 3 ≤ r) {H : Finset (Finset (Fin n))}
    (hUni : Uniform (r := r) H) (hLoc : LocalOne (r := r) H)
    {e₁ e₂ : Finset (Fin n)} (h₁ : e₁ ∈ H) (h₂ : e₂ ∈ H) :
    (e₁ ∩ e₂).Nonempty := by
  have hc1 : e₁.card = r := hUni e₁ h₁
  have hc2 : e₂.card = r := hUni e₂ h₂
  have hle : (e₁ ∪ e₂).card ≤ 3 * r - 3 := by
    have hu := Finset.card_union_le e₁ e₂
    rw [hc1, hc2] at hu
    omega
  obtain ⟨S, hS1, hS2⟩ := hLoc (e₁ ∪ e₂) hle
  obtain ⟨x, hx⟩ := hS2 e₁ h₁ (fun a ha => Finset.mem_union_left _ ha)
  obtain ⟨y, hy⟩ := hS2 e₂ h₂ (fun a ha => Finset.mem_union_right _ ha)
  rw [Finset.mem_inter] at hx hy
  have hxy : x = y := Finset.card_le_one.mp hS1 x hx.2 y hy.2
  exact ⟨x, Finset.mem_inter.mpr ⟨hx.1, by rw [hxy]; exact hy.1⟩⟩

/-- For `r ≥ 3`, ANY three edges of `H` share a common vertex.

Three pairwise-intersecting `r`-sets with no common vertex span at most `3r-3` vertices:
`|e₁ ∪ e₂| ≤ 2r-1`, and `e₃` meets `e₁ ∪ e₂` in at least two distinct points
(one in `e₁`, one in `e₂`; they differ precisely because there is no common vertex),
so `e₃` contributes at most `r-2` new ones.  `LocalOne` then supplies the common vertex. -/
theorem triple_common {r n : ℕ} (hr : 3 ≤ r) {H : Finset (Finset (Fin n))}
    (hUni : Uniform (r := r) H) (hLoc : LocalOne (r := r) H)
    {e₁ e₂ e₃ : Finset (Fin n)} (h₁ : e₁ ∈ H) (h₂ : e₂ ∈ H) (h₃ : e₃ ∈ H) :
    (e₁ ∩ e₂ ∩ e₃).Nonempty := by
  by_contra hcon
  have hc1 : e₁.card = r := hUni e₁ h₁
  have hc2 : e₂.card = r := hUni e₂ h₂
  have hc3 : e₃.card = r := hUni e₃ h₃
  obtain ⟨p, hp⟩ := pair_meet hr hUni hLoc h₁ h₃
  obtain ⟨q, hq⟩ := pair_meet hr hUni hLoc h₂ h₃
  rw [Finset.mem_inter] at hp hq
  have hpq : p ≠ q := by
    intro hEq
    refine hcon ⟨p, ?_⟩
    rw [Finset.mem_inter, Finset.mem_inter]
    exact ⟨⟨hp.1, by rw [hEq]; exact hq.1⟩, hp.2⟩
  have hint12 : 1 ≤ (e₁ ∩ e₂).card := Finset.card_pos.mpr (pair_meet hr hUni hLoc h₁ h₂)
  have hu12 : (e₁ ∪ e₂).card + (e₁ ∩ e₂).card = e₁.card + e₂.card :=
    Finset.card_union_add_card_inter e₁ e₂
  have hpair : ({p, q} : Finset (Fin n)) ⊆ (e₁ ∪ e₂) ∩ e₃ := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hp.1, hp.2⟩
    · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hq.1, hq.2⟩
  have hcard2 : 2 ≤ ((e₁ ∪ e₂) ∩ e₃).card := by
    have hsub := Finset.card_le_card hpair
    rwa [Finset.card_pair hpq] at hsub
  have hu123 : ((e₁ ∪ e₂) ∪ e₃).card + ((e₁ ∪ e₂) ∩ e₃).card = (e₁ ∪ e₂).card + e₃.card :=
    Finset.card_union_add_card_inter _ _
  have hle : ((e₁ ∪ e₂) ∪ e₃).card ≤ 3 * r - 3 := by omega
  obtain ⟨S, hS1, hS2⟩ := hLoc ((e₁ ∪ e₂) ∪ e₃) hle
  obtain ⟨x, hx⟩ := hS2 e₁ h₁ (fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _ ha))
  obtain ⟨y, hy⟩ := hS2 e₂ h₂ (fun a ha => Finset.mem_union_left _ (Finset.mem_union_right _ ha))
  obtain ⟨z, hz⟩ := hS2 e₃ h₃ (fun a ha => Finset.mem_union_right _ ha)
  rw [Finset.mem_inter] at hx hy hz
  have hxy : x = y := Finset.card_le_one.mp hS1 x hx.2 y hy.2
  have hxz : x = z := Finset.card_le_one.mp hS1 x hx.2 z hz.2
  refine hcon ⟨x, ?_⟩
  rw [Finset.mem_inter, Finset.mem_inter]
  exact ⟨⟨hx.1, by rw [hxy]; exact hy.1⟩, by rw [hxz]; exact hz.1⟩

/-! ## Part 4 — the case `r = 3` is completely decided: the answer is `t = 1` -/

/-- For `r = 3` the local hypothesis forces a global transversal of size one.

Suppose not.  Pick an edge `e = {a,b,c}` and edges `ea, eb, ec` avoiding `a, b, c`.
`triple_common` on `(e,ea,eb)`, `(e,ea,ec)`, `(e,eb,ec)` puts `{b,c} ⊆ ea`, `{a,c} ⊆ eb`,
`{a,b} ⊆ ec`; on `(ea,eb,ec)` it produces a vertex `w ∉ {a,b,c}` common to all three.
Cardinality then pins `ea = {b,c,w}`, `eb = {a,c,w}`, `ec = {a,b,w}`, so all four edges lie
inside `U = {a,b,c,w}` with `|U| = 4 ≤ 6 = 3r-3` — and those four have empty intersection,
contradicting `LocalOne` on `U`.  (The configuration is `K₄⁽³⁾`.) -/
theorem good_three_one : Good 3 1 := by
  unfold Good Claim CoverAtMost
  intro n H hUni hLoc
  by_contra hcon
  push_neg at hcon
  -- `H` is nonempty, else `∅` covers it
  have hne : H.Nonempty := by
    rcases H.eq_empty_or_nonempty with rfl | hne
    · have hcov : IsCover (∅ : Finset (Finset (Fin n))) (∅ : Finset (Fin n)) := by
        intro e he
        simp at he
      exact absurd hcov (hcon ∅ (by simp))
    · exact hne
  -- no vertex is a transversal
  have avoid : ∀ v : Fin n, ∃ f, f ∈ H ∧ v ∉ f := by
    intro v
    by_contra hno
    push_neg at hno
    exact hcon {v} (by simp) (fun e he => (meet_singleton_iff e v).mpr (hno e he))
  obtain ⟨e, he⟩ := hne
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp (hUni e he)
  obtain ⟨ea, hea, hnea⟩ := avoid a
  obtain ⟨eb, heb, hneb⟩ := avoid b
  obtain ⟨ec, hec, hnec⟩ := avoid c
  have h3 : (3 : ℕ) ≤ 3 := le_refl 3
  -- (e, ea, eb) : the common vertex can only be c
  have hcab : c ∈ ea ∧ c ∈ eb := by
    obtain ⟨v, hv⟩ := triple_common h3 hUni hLoc he hea heb
    rw [Finset.mem_inter, Finset.mem_inter] at hv
    have hve : v ∈ ({a, b, c} : Finset (Fin n)) := hv.1.1
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hve
    rcases hve with rfl | rfl | rfl
    · exact absurd hv.1.2 hnea
    · exact absurd hv.2 hneb
    · exact ⟨hv.1.2, hv.2⟩
  -- (e, ea, ec) : the common vertex can only be b
  have hbac : b ∈ ea ∧ b ∈ ec := by
    obtain ⟨v, hv⟩ := triple_common h3 hUni hLoc he hea hec
    rw [Finset.mem_inter, Finset.mem_inter] at hv
    have hve : v ∈ ({a, b, c} : Finset (Fin n)) := hv.1.1
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hve
    rcases hve with rfl | rfl | rfl
    · exact absurd hv.1.2 hnea
    · exact ⟨hv.1.2, hv.2⟩
    · exact absurd hv.2 hnec
  -- (e, eb, ec) : the common vertex can only be a
  have habc : a ∈ eb ∧ a ∈ ec := by
    obtain ⟨v, hv⟩ := triple_common h3 hUni hLoc he heb hec
    rw [Finset.mem_inter, Finset.mem_inter] at hv
    have hve : v ∈ ({a, b, c} : Finset (Fin n)) := hv.1.1
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hve
    rcases hve with rfl | rfl | rfl
    · exact ⟨hv.1.2, hv.2⟩
    · exact absurd hv.1.2 hneb
    · exact absurd hv.2 hnec
  -- (ea, eb, ec) : a fourth vertex w, distinct from a, b, c
  obtain ⟨w, hw⟩ := triple_common h3 hUni hLoc hea heb hec
  rw [Finset.mem_inter, Finset.mem_inter] at hw
  have hwa : w ≠ a := by rintro rfl; exact hnea hw.1.1
  have hwb : w ≠ b := by rintro rfl; exact hneb hw.1.2
  have hwc : w ≠ c := by rintro rfl; exact hnec hw.2
  -- cardinality pins the three avoiding edges
  have hcard_bcw : ({b, c, w} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.mpr ⟨b, c, w, hbc, fun h => hwb h.symm, fun h => hwc h.symm, rfl⟩
  have hcard_acw : ({a, c, w} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, c, w, hac, fun h => hwa h.symm, fun h => hwc h.symm, rfl⟩
  have hcard_abw : ({a, b, w} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, w, hab, fun h => hwa h.symm, fun h => hwb h.symm, rfl⟩
  have hea_eq : ea = ({b, c, w} : Finset (Fin n)) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hbac.1
      · exact hcab.1
      · exact hw.1.1
    · rw [hUni ea hea, hcard_bcw]
  have heb_eq : eb = ({a, c, w} : Finset (Fin n)) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact habc.1
      · exact hcab.2
      · exact hw.1.2
    · rw [hUni eb heb, hcard_acw]
  have hec_eq : ec = ({a, b, w} : Finset (Fin n)) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact habc.2
      · exact hbac.2
      · exact hw.2
    · rw [hUni ec hec, hcard_abw]
  -- all four edges live in a 4-element window
  have hUcard : ({a, b, c, w} : Finset (Fin n)).card ≤ 3 * 3 - 3 := by
    have k1 := Finset.card_insert_le a ({b, c, w} : Finset (Fin n))
    have k2 := Finset.card_insert_le b ({c, w} : Finset (Fin n))
    have k3 := Finset.card_insert_le c ({w} : Finset (Fin n))
    have k4 : ({w} : Finset (Fin n)).card = 1 := by simp
    omega
  obtain ⟨S, hS1, hS2⟩ := hLoc ({a, b, c, w} : Finset (Fin n)) hUcard
  have se : ({a, b, c} : Finset (Fin n)) ⊆ ({a, b, c, w} : Finset (Fin n)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have sea : ea ⊆ ({a, b, c, w} : Finset (Fin n)) := by
    rw [hea_eq]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have seb : eb ⊆ ({a, b, c, w} : Finset (Fin n)) := by
    rw [heb_eq]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have sec : ec ⊆ ({a, b, c, w} : Finset (Fin n)) := by
    rw [hec_eq]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  obtain ⟨x1, hx1⟩ := hS2 _ he se
  obtain ⟨x2, hx2⟩ := hS2 _ hea sea
  obtain ⟨x3, hx3⟩ := hS2 _ heb seb
  obtain ⟨x4, hx4⟩ := hS2 _ hec sec
  rw [Finset.mem_inter] at hx1 hx2 hx3 hx4
  have e12 : x1 = x2 := Finset.card_le_one.mp hS1 _ hx1.2 _ hx2.2
  have e13 : x1 = x3 := Finset.card_le_one.mp hS1 _ hx1.2 _ hx3.2
  have e14 : x1 = x4 := Finset.card_le_one.mp hS1 _ hx1.2 _ hx4.2
  have m2 : x1 ∈ ea := by rw [e12]; exact hx2.1
  have m3 : x1 ∈ eb := by rw [e13]; exact hx3.1
  have m4 : x1 ∈ ec := by rw [e14]; exact hx4.1
  have hmem : x1 ∈ ({a, b, c} : Finset (Fin n)) := hx1.1
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact hnea m2
  · exact hneb m3
  · exact hnec m4

/-- The exact answer for `r = 3`. -/
theorem optimal_three : Optimal 3 1 :=
  ⟨good_three_one, fun _ hu => good_one_le (by norm_num) hu⟩

theorem optimal_three_eq {t : ℚ} (h : Optimal 3 t) : t = 1 :=
  optimal_unique h optimal_three

/-! ## Part 5 — the stub's goal is refuted -/

/-- The `sorry`'d goal of `oracle/evidence/certified-corpus/erdos-616.lean` is FALSE.
At `r = 3` the optimum exists and equals `1`, but the claimed EHT lower bound demands
`3·3/16 + 7/8 = 23/16 > 1`.  (The claimed window is in fact empty for every `r < 70`.) -/
theorem erdos_616_stub_statement_is_false :
    ¬ (∀ r : ℕ, 3 ≤ r →
        ∃ t : ℚ, Optimal r t ∧
          ((3 : ℚ) / 16) * r + 7 / 8 ≤ t ∧
          t ≤ ((1 : ℚ) / 5) * r) := by
  intro h
  obtain ⟨t, hopt, hlo, _⟩ := h 3 (by norm_num)
  rw [optimal_three_eq hopt] at hlo
  norm_num at hlo

/-- Sharper: at `r = 3` the optimum is exactly `1`, so the EHT lower bound `3r/16 + 7/8`
is violated there — the failure is genuine, not an artefact of the empty window. -/
theorem eht_lower_bound_fails_at_three :
    ¬ (((3 : ℚ) / 16) * (3 : ℕ) + 7 / 8 ≤ 1) := by
  norm_num

/-! ## Part 6 — an explicit family showing the answer is at least `2` for every `r ≥ 6`

Write `r = m + 3`.  On the vertex set `Fin 4 × Fin (m+1)` (four blocks of `m+1` vertices)
put four edges:

`P i = {(j,0) : j ≠ i} ∪ ({i} × (block i minus its hub))`,

i.e. edge `i` takes the three *hubs* other than its own, plus all `m` non-hub vertices of its
own block.  Then `|P i| = 3 + m = r`; any three of the four share a hub; all four have empty
intersection; and their union is the whole vertex set, of size `4(m+1) = 4r-8`.  For `r ≥ 6`
that is strictly bigger than the window `3r-3`, so no admissible `U` can contain all four
edges — which is exactly what `LocalOne` needs, while the transversal number is `2`. -/

theorem exists_ne_fin4 (a : Fin 4) : ∃ j : Fin 4, j ≠ a := by
  by_cases h : a = 0
  · exact ⟨1, by rw [h]; decide⟩
  · exact ⟨0, fun hj => h hj.symm⟩

/-- The four edges in product coordinates. -/
def P (m : ℕ) (i : Fin 4) : Finset (Fin 4 × Fin (m + 1)) :=
  ((Finset.univ.erase i) ×ˢ ({0} : Finset (Fin (m + 1)))) ∪
    (({i} : Finset (Fin 4)) ×ˢ (Finset.univ.erase (0 : Fin (m + 1))))

theorem mem_P (m : ℕ) (i : Fin 4) (p : Fin 4 × Fin (m + 1)) :
    p ∈ P m i ↔ ((p.1 ≠ i ∧ p.2 = 0) ∨ (p.1 = i ∧ p.2 ≠ 0)) := by
  show p ∈ (((Finset.univ.erase i) ×ˢ ({0} : Finset (Fin (m + 1)))) ∪
    (({i} : Finset (Fin 4)) ×ˢ (Finset.univ.erase (0 : Fin (m + 1))))) ↔ _
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_erase, Finset.mem_singleton,
    Finset.mem_univ, and_true] <;> tauto

theorem card_P (m : ℕ) (i : Fin 4) : (P m i).card = m + 3 := by
  have hA : ((Finset.univ.erase i) ×ˢ ({0} : Finset (Fin (m + 1)))).card = 3 := by
    rw [Finset.card_product]
    simp
  have hB : ((({i} : Finset (Fin 4))) ×ˢ (Finset.univ.erase (0 : Fin (m + 1)))).card = m := by
    rw [Finset.card_product]
    simp
  have hI : (((Finset.univ.erase i) ×ˢ ({0} : Finset (Fin (m + 1)))) ∩
      ((({i} : Finset (Fin 4))) ×ˢ (Finset.univ.erase (0 : Fin (m + 1))))).card ≤ 0 := by
    have hsub : (((Finset.univ.erase i) ×ˢ ({0} : Finset (Fin (m + 1)))) ∩
        ((({i} : Finset (Fin 4))) ×ˢ (Finset.univ.erase (0 : Fin (m + 1))))) ⊆
          (∅ : Finset (Fin 4 × Fin (m + 1))) := by
      intro p hp
      rw [Finset.mem_inter] at hp
      exact absurd (Finset.mem_singleton.mp (Finset.mem_product.mp hp.2).1)
        (Finset.mem_erase.mp (Finset.mem_product.mp hp.1).1).1
    simpa using Finset.card_le_card hsub
  have hsum := Finset.card_union_add_card_inter
    ((Finset.univ.erase i) ×ˢ ({0} : Finset (Fin (m + 1))))
    ((({i} : Finset (Fin 4))) ×ˢ (Finset.univ.erase (0 : Fin (m + 1))))
  show (((Finset.univ.erase i) ×ˢ ({0} : Finset (Fin (m + 1)))) ∪
    (({i} : Finset (Fin 4)) ×ˢ (Finset.univ.erase (0 : Fin (m + 1))))).card = m + 3
  omega

/-- The same four edges, transported to `Fin (4*(m+1))`. -/
def E (m : ℕ) (i : Fin 4) : Finset (Fin (4 * (m + 1))) :=
  (P m i).map (finProdFinEquiv.toEmbedding)

theorem mem_E (m : ℕ) (i : Fin 4) (x : Fin (4 * (m + 1))) :
    x ∈ E m i ↔ (finProdFinEquiv.symm x) ∈ P m i := by
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ :=
      Finset.mem_map.mp (show x ∈ (P m i).map (finProdFinEquiv.toEmbedding) from hx)
    have hxp : finProdFinEquiv.symm x = p := by rw [← hpx]; simp
    rw [hxp]; exact hp
  · intro hx
    refine Finset.mem_map.mpr ⟨finProdFinEquiv.symm x, hx, ?_⟩
    simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply]

theorem card_E (m : ℕ) (i : Fin 4) : (E m i).card = m + 3 := by
  show ((P m i).map (finProdFinEquiv.toEmbedding)).card = m + 3
  rw [Finset.card_map, card_P]

/-- The four edges cover every vertex. -/
theorem cover_all (m : ℕ) (x : Fin (4 * (m + 1))) : ∃ i : Fin 4, x ∈ E m i := by
  by_cases h0 : (finProdFinEquiv.symm x).2 = 0
  · obtain ⟨j, hj⟩ := exists_ne_fin4 (finProdFinEquiv.symm x).1
    exact ⟨j, (mem_E m j x).mpr ((mem_P m j _).mpr (Or.inl ⟨hj.symm, h0⟩))⟩
  · exact ⟨(finProdFinEquiv.symm x).1,
      (mem_E m _ x).mpr ((mem_P m _ _).mpr (Or.inr ⟨rfl, h0⟩))⟩

/-- For `r = m + 3 ≥ 6` no admissible `t` can be below `2`. -/
theorem good_two_le {m : ℕ} (hm : 3 ≤ m) {t : ℚ} (h : Good (m + 3) t) : 2 ≤ t := by
  set H : Finset (Finset (Fin (4 * (m + 1)))) := Finset.image (E m) Finset.univ with hHdef
  have hmemH : ∀ e : Finset (Fin (4 * (m + 1))), e ∈ H ↔ ∃ i : Fin 4, E m i = e := by
    intro e
    rw [hHdef]
    simp [Finset.mem_image]
  have hUni : Uniform (r := m + 3) H := by
    intro e he
    obtain ⟨i, rfl⟩ := (hmemH e).mp he
    exact card_E m i
  have hLoc : LocalOne (r := m + 3) H := by
    intro U hU
    have hUc : U.card ≤ 3 * m + 6 := by omega
    have hnotall : ∃ i : Fin 4, ¬ (E m i ⊆ U) := by
      by_contra hall
      push_neg at hall
      have huniv : U = Finset.univ := by
        rw [Finset.eq_univ_iff_forall]
        intro x
        obtain ⟨i, hi⟩ := cover_all m x
        exact hall i hi
      rw [huniv, Finset.card_univ, Fintype.card_fin] at hUc
      omega
    obtain ⟨i, hi⟩ := hnotall
    refine ⟨{finProdFinEquiv (i, 0)}, by simp, ?_⟩
    intro e he hsub
    obtain ⟨j, rfl⟩ := (hmemH e).mp he
    have hji : j ≠ i := by rintro rfl; exact hi hsub
    refine ⟨finProdFinEquiv (i, 0), Finset.mem_inter.mpr ⟨?_, Finset.mem_singleton_self _⟩⟩
    refine (mem_E m j _).mpr ?_
    rw [Equiv.symm_apply_apply]
    exact (mem_P m j (i, 0)).mpr (Or.inl ⟨Ne.symm hji, rfl⟩)
  obtain ⟨S, hScard, hScov⟩ := h (4 * (m + 1)) H hUni hLoc
  by_contra hlt
  push_neg at hlt
  have hS1 : S.card ≤ 1 := by
    have hq : (S.card : ℚ) < 2 := lt_of_le_of_lt hScard hlt
    have hn : (S.card : ℕ) < 2 := by exact_mod_cast hq
    omega
  have hwit : ∀ j : Fin 4, ∃ y, y ∈ E m j ∧ y ∈ S := by
    intro j
    obtain ⟨y, hy⟩ := hScov (E m j) ((hmemH _).mpr ⟨j, rfl⟩)
    rw [Finset.mem_inter] at hy
    exact ⟨y, hy.1, hy.2⟩
  obtain ⟨x0, hx0E, hx0S⟩ := hwit 0
  have hall : ∀ j : Fin 4, x0 ∈ E m j := by
    intro j
    obtain ⟨y, hyE, hyS⟩ := hwit j
    have hxy : x0 = y := Finset.card_le_one.mp hS1 x0 hx0S y hyS
    rw [hxy]; exact hyE
  have h1 : (finProdFinEquiv.symm x0).2 ≠ 0 := by
    rcases (mem_P m (finProdFinEquiv.symm x0).1 _).mp
        ((mem_E m (finProdFinEquiv.symm x0).1 x0).mp (hall _)) with ⟨hne, _⟩ | ⟨_, hne⟩
    · exact absurd rfl hne
    · exact hne
  obtain ⟨j, hj⟩ := exists_ne_fin4 (finProdFinEquiv.symm x0).1
  have h2 : (finProdFinEquiv.symm x0).2 = 0 := by
    rcases (mem_P m j _).mp ((mem_E m j x0).mp (hall j)) with ⟨_, hz⟩ | ⟨hz, _⟩
    · exact hz
    · exact absurd hz hj.symm
  exact h1 h2

theorem good_two_le' {r : ℕ} (hr : 6 ≤ r) {t : ℚ} (h : Good r t) : 2 ≤ t := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 3 := ⟨r - 3, by omega⟩
  exact good_two_le (by omega) h

/-! ## Part 7 — the transcribed EHT upper bound `t ≤ r/5` is refuted by real instances -/

/-- For `1 ≤ r < 5` the optimum is `≥ 1 > r/5`. -/
theorem eht_upper_fails_lt_five {r : ℕ} (hr0 : 0 < r) (hr : r < 5) :
    ¬ ∃ t : ℚ, Good r t ∧ t ≤ ((1 : ℚ) / 5) * r := by
  rintro ⟨t, hg, hub⟩
  have h1 : (1 : ℚ) ≤ t := good_one_le hr0 hg
  have hrq : (r : ℚ) < 5 := by exact_mod_cast hr
  linarith

/-- For `6 ≤ r < 10` the optimum is `≥ 2 > r/5`. -/
theorem eht_upper_fails_six_to_nine {r : ℕ} (hr : 6 ≤ r) (hr' : r < 10) :
    ¬ ∃ t : ℚ, Good r t ∧ t ≤ ((1 : ℚ) / 5) * r := by
  rintro ⟨t, hg, hub⟩
  have h2 : (2 : ℚ) ≤ t := good_two_le' hr hg
  have hrq : (r : ℚ) < 10 := by exact_mod_cast hr'
  linarith

/-- The stub goal also fails at `r = 6`, and there the failure is carried by a real
hypergraph: the optimum is `≥ 2`, while the claimed upper bound is `6/5`. -/
theorem stub_fails_at_six :
    ¬ ∃ t : ℚ, Optimal 6 t ∧
        ((3 : ℚ) / 16) * (6 : ℕ) + 7 / 8 ≤ t ∧ t ≤ ((1 : ℚ) / 5) * (6 : ℕ) := by
  rintro ⟨t, hopt, _, hub⟩
  exact eht_upper_fails_six_to_nine (by norm_num) (by norm_num) ⟨t, hopt.1, hub⟩

/-- `Good r 1` holds at `r = 3` and fails for every `r ≥ 6`. -/
theorem good_one_fails_of_six_le {r : ℕ} (hr : 6 ≤ r) : ¬ Good r 1 := by
  intro h
  have := good_two_le' hr h
  norm_num at this

/-! ## Part 8 — the Helly argument: for `3 ≤ r ≤ 5` the optimum is exactly `1`

Let `F` be a MINIMAL subfamily with no common vertex.  For each `e ∈ F` the rest of `F` has a
common vertex `w e`, and `w e ∉ e` (else it would serve for all of `F`).  Those vertices are
distinct, so with `m = |F|` every edge of `F` contains the `m-1` vertices `w f`, `f ≠ e`, and
therefore has at most `r-m+1` vertices outside `W = {w f}`.  Hence

`|⋃ F| ≤ m + m(r-m+1)`,

and for `3 ≤ r ≤ 5` this is `≤ 3r-3` for EVERY `2 ≤ m ≤ r+1` — so `LocalOne` applies to `⋃ F`
and hands back the common vertex that `F` was supposed not to have. -/

theorem union_bound_arith {r m : ℕ} (hr3 : 3 ≤ r) (hr5 : r ≤ 5) (hm2 : 2 ≤ m)
    (hmr : m ≤ r + 1) : m + m * (r + 1 - m) ≤ 3 * r - 3 := by
  interval_cases r <;> interval_cases m <;> omega

theorem helly_small {r n : ℕ} (hr3 : 3 ≤ r) (hr5 : r ≤ 5) {H : Finset (Finset (Fin n))}
    (hUni : Uniform (r := r) H) (hLoc : LocalOne (r := r) H) :
    ∀ F : Finset (Finset (Fin n)), F ⊆ H → F.Nonempty → ∃ v : Fin n, ∀ e ∈ F, v ∈ e := by
  suffices key : ∀ k : ℕ, ∀ F : Finset (Finset (Fin n)), F.card ≤ k → F ⊆ H → F.Nonempty →
      ∃ v : Fin n, ∀ e ∈ F, v ∈ e by
    intro F hFH hFne
    exact key F.card F (le_refl _) hFH hFne
  intro k
  induction k with
  | zero =>
    intro F hcard _ hFne
    exact absurd (Finset.card_pos.mpr hFne) (by omega)
  | succ k ih =>
    intro F hcard hFH hFne
    by_contra hcon
    push_neg at hcon
    obtain ⟨e0, he0⟩ := hFne
    have hone : ∀ e ∈ F, e.Nonempty := by
      intro e he
      have hc : e.card = r := hUni e (hFH he)
      exact Finset.card_pos.mp (by omega)
    -- a single edge always has a common vertex, so `|F| ≥ 2`
    have hcard2 : 2 ≤ F.card := by
      by_contra hlt
      push_neg at hlt
      have hc1 : F.card = 1 := by
        have hp := Finset.card_pos.mpr ⟨e0, he0⟩
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
      have hea : e0 = a := by
        have h' := he0
        rw [ha, Finset.mem_singleton] at h'
        exact h'
      obtain ⟨v, hv⟩ := hone e0 he0
      obtain ⟨f, hfF, hvf⟩ := hcon v
      rw [ha, Finset.mem_singleton] at hfF
      exact hvf (by rw [hfF, ← hea]; exact hv)
    obtain ⟨x0v, _⟩ := hone e0 he0
    -- for each edge, a vertex common to all the OTHERS but missing from it
    have hv : ∀ e : Finset (Fin n), ∃ x : Fin n,
        e ∈ F → ((∀ f ∈ F.erase e, x ∈ f) ∧ x ∉ e) := by
      intro e
      by_cases he : e ∈ F
      · have hsub : F.erase e ⊆ H := fun z hz => hFH (Finset.mem_of_mem_erase hz)
        have hne : (F.erase e).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem he]
          omega
        have hcle : (F.erase e).card ≤ k := by
          rw [Finset.card_erase_of_mem he]
          omega
        obtain ⟨u, hu⟩ := ih (F.erase e) hcle hsub hne
        refine ⟨u, fun _ => ⟨hu, ?_⟩⟩
        intro hue
        obtain ⟨g, hgF, hug⟩ := hcon u
        rcases eq_or_ne g e with rfl | hge
        · exact hug hue
        · exact hug (hu g (Finset.mem_erase.mpr ⟨hge, hgF⟩))
      · exact ⟨x0v, fun h => absurd h he⟩
    choose w hw using hv
    -- those vertices are pairwise distinct
    have hinj : ∀ e ∈ F, ∀ f ∈ F, w e = w f → e = f := by
      intro e he f hf hwef
      by_contra hef
      have h1 : w e ∈ f := (hw e he).1 f (Finset.mem_erase.mpr ⟨Ne.symm hef, hf⟩)
      rw [hwef] at h1
      exact (hw f hf).2 h1
    have hcardW : (F.image w).card = F.card :=
      Finset.card_image_of_injOn (fun e he f hf hwef =>
        hinj e (Finset.mem_coe.mp he) f (Finset.mem_coe.mp hf) hwef)
    have hWsub : ∀ f ∈ F, ((F.image w).erase (w f)) ⊆ f := by
      intro f hf x hx
      rw [Finset.mem_erase] at hx
      obtain ⟨e, he, hex⟩ := Finset.mem_image.mp hx.2
      have hef : f ≠ e := by
        intro h
        exact hx.1 (by rw [h, hex])
      rw [← hex]
      exact (hw e he).1 f (Finset.mem_erase.mpr ⟨hef, hf⟩)
    -- hence each edge has at most `r - (m-1)` vertices outside `W`
    have hfW : ∀ f ∈ F, (f \ (F.image w)).card + (F.card - 1) ≤ r := by
      intro f hf
      have hsub : ((F.image w).erase (w f)) ∪ (f \ (F.image w)) ⊆ f := by
        intro x hx
        rcases Finset.mem_union.mp hx with h | h
        · exact hWsub f hf h
        · exact (Finset.mem_sdiff.mp h).1
      have hdisj : (((F.image w).erase (w f)) ∩ (f \ (F.image w))).card ≤ 0 := by
        have hs : (((F.image w).erase (w f)) ∩ (f \ (F.image w))) ⊆ (∅ : Finset (Fin n)) := by
          intro x hx
          rw [Finset.mem_inter] at hx
          exact absurd (Finset.mem_of_mem_erase hx.1) (Finset.mem_sdiff.mp hx.2).2
        simpa using Finset.card_le_card hs
      have hsum := Finset.card_union_add_card_inter
        ((F.image w).erase (w f)) (f \ (F.image w))
      have hle := Finset.card_le_card hsub
      have hce : ((F.image w).erase (w f)).card = F.card - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_image_of_mem w hf), hcardW]
      have hfc : f.card = r := hUni f (hFH hf)
      omega
    -- so the union of `F` fits inside a legal window
    have hmr : F.card ≤ r + 1 := by
      have hce : ((F.image w).erase (w e0)).card = F.card - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_image_of_mem w he0), hcardW]
      have hcl := Finset.card_le_card (hWsub e0 he0)
      have hfc : e0.card = r := hUni e0 (hFH he0)
      omega
    have hbig : (F.biUnion id).card ≤ 3 * r - 3 := by
      have hsub : F.biUnion id ⊆
          (F.image w) ∪ (F.biUnion (fun f => f \ (F.image w))) := by
        intro x hx
        obtain ⟨f, hf, hxf⟩ := Finset.mem_biUnion.mp hx
        by_cases hxW : x ∈ F.image w
        · exact Finset.mem_union_left _ hxW
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_sdiff.mpr ⟨hxf, hxW⟩⟩)
      have h3 : (F.biUnion (fun f => f \ (F.image w))).card ≤ F.card * (r + 1 - F.card) :=
        Finset.card_biUnion_le_card_mul F _ _ (fun f hf => by have := hfW f hf; omega)
      calc (F.biUnion id).card
          ≤ ((F.image w) ∪ (F.biUnion (fun f => f \ (F.image w)))).card :=
            Finset.card_le_card hsub
        _ ≤ (F.image w).card + (F.biUnion (fun f => f \ (F.image w))).card :=
            Finset.card_union_le _ _
        _ ≤ F.card + F.card * (r + 1 - F.card) := by
            rw [hcardW]
            exact Nat.add_le_add_left h3 _
        _ ≤ 3 * r - 3 := union_bound_arith hr3 hr5 hcard2 hmr
    -- and `LocalOne` on that window returns the common vertex `F` was supposed to lack
    obtain ⟨S, hS1, hS2⟩ := hLoc (F.biUnion id) hbig
    have hsubU : ∀ f ∈ F, f ⊆ F.biUnion id := by
      intro f hf x hx
      exact Finset.mem_biUnion.mpr ⟨f, hf, hx⟩
    obtain ⟨x, hx⟩ := hS2 e0 (hFH he0) (hsubU e0 he0)
    rw [Finset.mem_inter] at hx
    obtain ⟨g, hgF, hxg⟩ := hcon x
    obtain ⟨y, hy⟩ := hS2 g (hFH hgF) (hsubU g hgF)
    rw [Finset.mem_inter] at hy
    have hxy : x = y := Finset.card_le_one.mp hS1 x hx.2 y hy.2
    rw [hxy] at hxg
    exact hxg hy.1

theorem good_one_of_le_five {r : ℕ} (hr3 : 3 ≤ r) (hr5 : r ≤ 5) : Good r 1 := by
  unfold Good Claim CoverAtMost
  intro n H hUni hLoc
  rcases H.eq_empty_or_nonempty with rfl | hne
  · refine ⟨∅, by simp, ?_⟩
    intro e he
    simp at he
  · obtain ⟨v, hv⟩ := helly_small hr3 hr5 hUni hLoc H (Finset.Subset.refl H) hne
    refine ⟨{v}, by simp, ?_⟩
    intro e he
    exact ⟨v, Finset.mem_inter.mpr ⟨hv e he, Finset.mem_singleton_self v⟩⟩

/-- Complete determination of the optimum for every `r` in `{3,4,5}`. -/
theorem optimal_of_le_five {r : ℕ} (hr3 : 3 ≤ r) (hr5 : r ≤ 5) : Optimal r 1 :=
  ⟨good_one_of_le_five hr3 hr5, fun _ hu => good_one_le (by omega) hu⟩

/-- The exact threshold: for `r ≥ 3`, a transversal of size one always suffices
precisely when `r ≤ 5`. -/
theorem good_one_iff {r : ℕ} (hr : 3 ≤ r) : Good r 1 ↔ r ≤ 5 := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    exact good_one_fails_of_six_le (by omega) h
  · intro h
    exact good_one_of_le_five hr h

/-- The stub goal fails at every `r` in `{3,4,5}`: there the optimum is exactly `1`,
which is below the claimed lower bound `3r/16 + 7/8` for `r ≤ 5`. -/
theorem stub_fails_of_le_five {r : ℕ} (hr3 : 3 ≤ r) (hr5 : r ≤ 5) :
    ¬ ∃ t : ℚ, Optimal r t ∧
        ((3 : ℚ) / 16) * r + 7 / 8 ≤ t ∧ t ≤ ((1 : ℚ) / 5) * r := by
  rintro ⟨t, hopt, _, hub⟩
  have ht : t = 1 := optimal_unique hopt (optimal_of_le_five hr3 hr5)
  have hrq : (r : ℚ) ≤ 5 := by exact_mod_cast hr5
  rw [ht] at hub
  linarith

/-! ## The whole result of this attack, as one checkable declaration -/

theorem ERDOS_616_ATTACK_2026_09_05 :
    -- (1) for every `r` in `{3,4,5}` the optimum EXISTS and is exactly `1`
    (∀ r : ℕ, 3 ≤ r → r ≤ 5 → Optimal r 1) ∧
    -- (2) for every `r ≥ 6` no admissible `t` is below `2` (explicit 4-edge family)
    (∀ r : ℕ, 6 ≤ r → ∀ t : ℚ, Good r t → 2 ≤ t) ∧
    -- (3) so `Good r 1` holds exactly for `3 ≤ r ≤ 5`
    (∀ r : ℕ, 3 ≤ r → (Good r 1 ↔ r ≤ 5)) ∧
    -- (4) the claimed EHT window `[3r/16 + 7/8, r/5]` is EMPTY for every `r < 70`
    (∀ r : ℕ, r < 70 → ¬ ∃ t : ℚ, ((3 : ℚ) / 16) * r + 7 / 8 ≤ t ∧ t ≤ ((1 : ℚ) / 5) * r) ∧
    -- (5) the transcribed UPPER bound `t ≤ r/5` is refuted by real instances,
    --     for `1 ≤ r < 5` and again for `6 ≤ r < 10`
    (∀ r : ℕ, 0 < r → r < 5 → ¬ ∃ t : ℚ, Good r t ∧ t ≤ ((1 : ℚ) / 5) * r) ∧
    (∀ r : ℕ, 6 ≤ r → r < 10 → ¬ ∃ t : ℚ, Good r t ∧ t ≤ ((1 : ℚ) / 5) * r) ∧
    -- (6) hence the stub's `sorry`'d goal is FALSE
    ¬ (∀ r : ℕ, 3 ≤ r →
        ∃ t : ℚ, Optimal r t ∧
          ((3 : ℚ) / 16) * r + 7 / 8 ≤ t ∧
          t ≤ ((1 : ℚ) / 5) * r) :=
  ⟨fun _ h3 h5 => optimal_of_le_five h3 h5,
   fun _ h6 _ hg => good_two_le' h6 hg,
   fun _ h3 => good_one_iff h3,
   fun _ h => window_empty_of_lt_seventy _ h,
   fun _ h0 h5 => eht_upper_fails_lt_five h0 h5,
   fun _ h6 h9 => eht_upper_fails_six_to_nine h6 h9,
   erdos_616_stub_statement_is_false⟩

end

#print axioms window_nonempty_iff
#print axioms window_empty_of_lt_seventy
#print axioms window_refutation
#print axioms meet_singleton_iff
#print axioms good_mono
#print axioms good_one_le
#print axioms optimal_unique
#print axioms pair_meet
#print axioms triple_common
#print axioms good_three_one
#print axioms optimal_three
#print axioms optimal_three_eq
#print axioms erdos_616_stub_statement_is_false
#print axioms eht_lower_bound_fails_at_three
#print axioms exists_ne_fin4
#print axioms mem_P
#print axioms card_P
#print axioms mem_E
#print axioms card_E
#print axioms cover_all
#print axioms good_two_le
#print axioms good_two_le'
#print axioms eht_upper_fails_lt_five
#print axioms eht_upper_fails_six_to_nine
#print axioms stub_fails_at_six
#print axioms good_one_fails_of_six_le
#print axioms union_bound_arith
#print axioms helly_small
#print axioms good_one_of_le_five
#print axioms optimal_of_le_five
#print axioms good_one_iff
#print axioms stub_fails_of_le_five
#print axioms ERDOS_616_ATTACK_2026_09_05
