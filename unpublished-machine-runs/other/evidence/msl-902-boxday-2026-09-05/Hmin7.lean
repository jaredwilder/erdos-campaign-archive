import Mathlib

/-!
# ERDOS 902 / CONTRACT D — the descent floor for `hmin23`.

Kernel-sealing of node K2 of the CONTRACT D campaign: in an `S 4` tournament, for
every vertex `v` and every `u` in `H = inN v`, the in-degree of `u` INSIDE `H` is at
least seven.

* `hasSOn_descend`        `S (k+1)` on `H` gives `S k` on `H ∩ inN u`.
* `card_ge_three_of_pred` a nonempty set in which every member is beaten from inside
                          has at least three members.
* `card_ge_seven_of_S2`   `f 2 ≥ 7`, proved from the tournament axioms, not cited.
* `indegH_ge_seven`       the campaign lemma K2.

No `sorry`, no `native_decide`.
-/

namespace Erdos902Hmin

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : V → V → Prop) [DecidableRel T]

/-- `S k` relativized to a vertex set. -/
def HasSOn (H : Finset V) (k : ℕ) : Prop :=
  ∀ s : Finset V, s ⊆ H → s.card = k → ∃ u ∈ H, u ∉ s ∧ ∀ w ∈ s, T u w

/-- the in-neighbourhood of `x` INSIDE `W`. -/
def inW (W : Finset V) (x : V) : Finset V := W.filter (fun u => T u x)

/-- the out-neighbourhood of `x` INSIDE `W`. -/
def outW (W : Finset V) (x : V) : Finset V := W.filter (fun u => T x u)

/-- DESCENT. `S (k+1)` on `H` forces `S k` on the in-neighbourhood of any `u ∈ H`
taken inside `H`. -/
theorem hasSOn_descend (hirr : ∀ x : V, ¬ T x x) {H : Finset V} {k : ℕ}
    (hH : HasSOn T H (k + 1)) {u : V} (hu : u ∈ H) :
    HasSOn T (inW T H u) k := by
  intro q hq hqk
  have hqH : q ⊆ H := fun a ha => (Finset.mem_filter.mp (hq ha)).1
  have huq : u ∉ q := fun h => hirr u (Finset.mem_filter.mp (hq h)).2
  have hsub : insert u q ⊆ H := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hu
    · exact hqH ha
  have hcard : (insert u q).card = k + 1 := by
    rw [Finset.card_insert_of_notMem huq, hqk]
  obtain ⟨w, hwH, hw_not, hw_dom⟩ := hH (insert u q) hsub hcard
  refine ⟨w, Finset.mem_filter.mpr ⟨hwH, hw_dom u (Finset.mem_insert_self u q)⟩, ?_, ?_⟩
  · exact fun h => hw_not (Finset.mem_insert_of_mem h)
  · exact fun z hz => hw_dom z (Finset.mem_insert_of_mem hz)

/-- a nonempty set in which every member is beaten from inside has at least three
members. -/
theorem card_ge_three_of_pred (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    {A : Finset V} (hne : A.Nonempty) (hin : ∀ y ∈ A, ∃ u ∈ A, T u y) :
    3 ≤ A.card := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨u, hu, hua⟩ := hin a ha
  have hua_ne : u ≠ a := fun h => hirr a (h ▸ hua)
  obtain ⟨w, hw, hwu⟩ := hin u hu
  have hwu_ne : w ≠ u := fun h => hirr u (h ▸ hwu)
  have hwa : w ≠ a := by
    intro h; subst h; exact hasym _ _ hua hwu
  have hsub : ({a, u, w} : Finset V) ⊆ A := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hu
    · exact hw
  have hc : ({a, u, w} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hua_ne, Ne.symm hwa]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hwu_ne]), Finset.card_singleton]
  calc 3 = ({a, u, w} : Finset V).card := hc.symm
    _ ≤ A.card := Finset.card_le_card hsub

/-- the in/out split inside `W`. -/
theorem card_inW_add_card_outW (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    (W : Finset V) {x : V} (hx : x ∈ W) :
    (inW T W x).card + (outW T W x).card = W.card - 1 := by
  have hdisj : Disjoint (inW T W x) (outW T W x) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [inW, Finset.mem_filter] at ha
    rw [outW, Finset.mem_filter] at hb
    exact hasym _ _ ha.2 hb.2
  have hun : inW T W x ∪ outW T W x = W.erase x := by
    ext a
    rw [Finset.mem_union, inW, outW, Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hm, h⟩ | ⟨hm, h⟩)
      · exact ⟨fun hax => hirr x (hax ▸ h), hm⟩
      · exact ⟨fun hax => hirr x (hax ▸ h), hm⟩
    · rintro ⟨hne, hm⟩
      rcases htot a x hne with h | h
      · exact Or.inl ⟨hm, h⟩
      · exact Or.inr ⟨hm, h⟩
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hun, Finset.card_erase_of_mem hx] at hcard
  omega

/-- the restricted handshake: total in-degree inside `W` equals total out-degree. -/
theorem sum_inW_eq_sum_outW (W : Finset V) :
    ∑ x ∈ W, (inW T W x).card = ∑ x ∈ W, (outW T W x).card := by
  simp only [inW, outW, Finset.card_filter]
  exact Finset.sum_comm

/-- `f 2 ≥ 7`, PROVED. A vertex set carrying `S 2` with at least two members has at
least seven members. -/
theorem card_ge_seven_of_S2 (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    {W : Finset V} (hW : HasSOn T W 2) (h2 : 2 ≤ W.card) :
    7 ≤ W.card := by
  have key : ∀ x ∈ W, 3 ≤ (inW T W x).card := by
    intro x hx
    have pairdom : ∀ y ∈ W, y ≠ x → ∃ u ∈ W, T u x ∧ T u y := by
      intro y hy hyx
      have hsub : ({x, y} : Finset V) ⊆ W := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      have hc : ({x, y} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hyx]), Finset.card_singleton]
      obtain ⟨u, huW, _, hu_dom⟩ := hW _ hsub hc
      exact ⟨u, huW, hu_dom x (by simp), hu_dom y (by simp)⟩
    have hne : (inW T W x).Nonempty := by
      obtain ⟨y, hy, hyx⟩ : ∃ y ∈ W, y ≠ x := by
        have h1 : 1 < W.card := by omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
        by_cases h : a = x
        · exact ⟨b, hb, by rw [← h]; exact Ne.symm hab⟩
        · exact ⟨a, ha, h⟩
      obtain ⟨u, huW, hux, _⟩ := pairdom y hy hyx
      exact ⟨u, Finset.mem_filter.mpr ⟨huW, hux⟩⟩
    have hin : ∀ y ∈ inW T W x, ∃ u ∈ inW T W x, T u y := by
      intro y hy
      obtain ⟨hyW, hyx⟩ := Finset.mem_filter.mp hy
      have hyne : y ≠ x := fun h => hirr x (h ▸ hyx)
      obtain ⟨u, huW, hux, huy⟩ := pairdom y hyW hyne
      exact ⟨u, Finset.mem_filter.mpr ⟨huW, hux⟩, huy⟩
    exact card_ge_three_of_pred T hirr hasym hne hin
  have hlow : W.card * 3 ≤ ∑ x ∈ W, (inW T W x).card := by
    have h := Finset.card_nsmul_le_sum W (fun x => (inW T W x).card) 3 key
    rwa [smul_eq_mul] at h
  have hsplit : ∑ x ∈ W, ((inW T W x).card + (outW T W x).card) = W.card * (W.card - 1) := by
    rw [Finset.sum_congr rfl (fun x hx => card_inW_add_card_outW T hirr hasym htot W hx),
      Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← sum_inW_eq_sum_outW] at hsplit
  obtain ⟨m, hm⟩ : ∃ m, W.card = m + 1 := ⟨W.card - 1, by omega⟩
  rw [hm] at hsplit hlow ⊢
  simp only [Nat.add_sub_cancel] at hsplit
  nlinarith [hlow, hsplit]

/-- pick a third vertex. -/
theorem exists_third {H : Finset V} (h3 : 3 ≤ H.card) {u y : V}
    (hu : u ∈ H) (hy : y ∈ H) (huy : u ≠ y) :
    ∃ z ∈ H, z ≠ u ∧ z ≠ y := by
  have hcard : 0 < ((H.erase u).erase y).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm huy, hy⟩),
      Finset.card_erase_of_mem hu]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
  obtain ⟨hzy, hz'⟩ := Finset.mem_erase.mp hz
  obtain ⟨hzu, hzH⟩ := Finset.mem_erase.mp hz'
  exact ⟨z, hzH, hzu, hzy⟩

/-- NODE K2. In a vertex set `H` carrying `S 3` with at least three members, every
member has in-degree at least SEVEN inside `H`. -/
theorem indegH_ge_seven (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    {H : Finset V} (hH : HasSOn T H 3) (h3 : 3 ≤ H.card) {u : V} (hu : u ∈ H) :
    7 ≤ (inW T H u).card := by
  have hS2 : HasSOn T (inW T H u) 2 := hasSOn_descend T hirr hH hu
  have tripdom : ∀ y ∈ H, y ≠ u → ∃ w ∈ H, T w u ∧ T w y := by
    intro y hy hyu
    obtain ⟨z, hzH, hzu, hzy⟩ := exists_third h3 hu hy (Ne.symm hyu)
    have hsub : ({u, y, z} : Finset V) ⊆ H := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hu
      · exact hy
      · exact hzH
    have hc : ({u, y, z} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hyu, Ne.symm hzu]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hzy]), Finset.card_singleton]
    obtain ⟨w, hwH, _, hw_dom⟩ := hH _ hsub hc
    exact ⟨w, hwH, hw_dom u (by simp), hw_dom y (by simp)⟩
  have hAne : (inW T H u).Nonempty := by
    obtain ⟨y, hy, hyu⟩ : ∃ y ∈ H, y ≠ u := by
      have h1 : 1 < H.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
      by_cases h : a = u
      · exact ⟨b, hb, by rw [← h]; exact Ne.symm hab⟩
      · exact ⟨a, ha, h⟩
    obtain ⟨w, hwH, hwu, _⟩ := tripdom y hy hyu
    exact ⟨w, Finset.mem_filter.mpr ⟨hwH, hwu⟩⟩
  have hAin : ∀ y ∈ inW T H u, ∃ w ∈ inW T H u, T w y := by
    intro y hy
    obtain ⟨hyH, hyu⟩ := Finset.mem_filter.mp hy
    have hyne : y ≠ u := fun h => hirr u (h ▸ hyu)
    obtain ⟨w, hwH, hwu, hwy⟩ := tripdom y hyH hyne
    exact ⟨w, Finset.mem_filter.mpr ⟨hwH, hwu⟩, hwy⟩
  have hA3 : 3 ≤ (inW T H u).card := card_ge_three_of_pred T hirr hasym hAne hAin
  exact card_ge_seven_of_S2 T hirr hasym htot hS2 (by omega)

end Erdos902Hmin

#print axioms Erdos902Hmin.hasSOn_descend
#print axioms Erdos902Hmin.card_ge_seven_of_S2
#print axioms Erdos902Hmin.indegH_ge_seven
