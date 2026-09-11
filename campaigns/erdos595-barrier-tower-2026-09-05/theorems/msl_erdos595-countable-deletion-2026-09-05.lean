import Mathlib

set_option autoImplicit false

namespace Erdos595Apex

variable {V : Type*}

def Coverable (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧
    G.edgeSet ⊆ ⋃ n, (H n).edgeSet

theorem cliqueFree_three_iff (G : SimpleGraph V) :
    G.CliqueFree 3 ↔ ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z → False := by
  classical
  constructor
  · intro hG x y z hxy hyz hxz
    exact hG {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  · intro h s hs
    obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hs.2
    subst hset
    exact h x y z (hs.1 (by simp) (by simp) hxy) (hs.1 (by simp) (by simp) hyz)
      (hs.1 (by simp) (by simp) hxz)

def star (G : SimpleGraph V) (v : V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => x = v ∧ G.Adj x y)

theorem star_le (G : SimpleGraph V) (v : V) : star G v ≤ G := by
  intro x y h
  simp only [star, SimpleGraph.fromRel_adj] at h
  rcases h with ⟨-, ⟨-, ha⟩ | ⟨-, ha⟩⟩
  · exact ha
  · exact ha.symm

theorem star_adj_endpoint (G : SimpleGraph V) (v : V) :
    ∀ x y : V, (star G v).Adj x y → x = v ∨ y = v := by
  intro x y h
  simp only [star, SimpleGraph.fromRel_adj] at h
  rcases h with ⟨-, ⟨hx, -⟩ | ⟨hy, -⟩⟩
  · exact Or.inl hx
  · exact Or.inr hy

theorem star_cliqueFree (G : SimpleGraph V) (v : V) : (star G v).CliqueFree 3 := by
  rw [cliqueFree_three_iff]
  intro x y z hxy hyz hxz
  have key := star_adj_endpoint G v
  have hxyne : x ≠ y := hxy.ne
  have hyzne : y ≠ z := hyz.ne
  have hxzne : x ≠ z := hxz.ne
  rcases key x y hxy with hx | hy
  · rcases key y z hyz with hy' | hz'
    · exact hxyne (hx.trans hy'.symm)
    · exact hxzne (hx.trans hz'.symm)
  · rcases key x z hxz with hx' | hz'
    · exact hxyne (hx'.trans hy.symm)
    · exact hyzne (hy.trans hz'.symm)

theorem star_mem_edgeSet (G : SimpleGraph V) (v y : V) (h : G.Adj v y) :
    s(v, y) ∈ (star G v).edgeSet := by
  apply (star G v).mem_edgeSet.mpr
  show (SimpleGraph.fromRel fun a b => a = v ∧ G.Adj a b).Adj v y
  rw [SimpleGraph.fromRel_adj]
  exact ⟨G.ne_of_adj h, Or.inl ⟨rfl, h⟩⟩

theorem coverable_of_countable_deletion (G : SimpleGraph V) (S : Set V)
    (hS : S.Countable)
    (hrest : Coverable (SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → x ∉ S})) :
    Coverable G := by
  classical
  set G0 : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → x ∉ S}
    with hG0
  have hG0le : G0 ≤ G := by
    intro x y h
    rw [hG0, SimpleGraph.fromEdgeSet_adj] at h
    exact G.mem_edgeSet.mp h.1.1
  obtain ⟨H, hHle, hHfree, hHcov⟩ := hrest
  rcases Set.eq_empty_or_nonempty S with hemp | hne
  · refine ⟨H, fun n => le_trans (hHle n) hG0le, hHfree, ?_⟩
    intro e he
    apply hHcov
    rw [hG0, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨he, ?_⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩
    intro x _
    rw [hemp]
    exact Set.notMem_empty x
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hne
    refine ⟨fun n => if n % 2 = 0 then H (n / 2) else star G (f (n / 2)), ?_, ?_, ?_⟩
    · intro n
      by_cases hn : n % 2 = 0
      · simp only [hn, if_pos]
        exact le_trans (hHle (n / 2)) hG0le
      · simp only [hn, if_neg, if_false]
        exact star_le G (f (n / 2))
    · intro n
      by_cases hn : n % 2 = 0
      · simp only [hn, if_pos]
        exact hHfree (n / 2)
      · simp only [hn, if_neg, if_false]
        exact star_cliqueFree G (f (n / 2))
    · intro e he
      induction e using Sym2.ind with
      | _ x y =>
        have hadj : G.Adj x y := G.mem_edgeSet.mp he
        by_cases hxS : x ∈ S
        · obtain ⟨n, hn⟩ : ∃ n, f n = x := by
            have : x ∈ Set.range f := by rw [← hf]; exact hxS
            exact this
          refine Set.mem_iUnion.mpr ⟨2 * n + 1, ?_⟩
          have h1 : (2 * n + 1) % 2 = 1 := by omega
          have h2 : (2 * n + 1) / 2 = n := by omega
          simp only [h1, h2, Nat.one_ne_zero, if_neg, if_false]
          rw [hn]
          exact star_mem_edgeSet G x y hadj
        · by_cases hyS : y ∈ S
          · obtain ⟨n, hn⟩ : ∃ n, f n = y := by
              have : y ∈ Set.range f := by rw [← hf]; exact hyS
              exact this
            refine Set.mem_iUnion.mpr ⟨2 * n + 1, ?_⟩
            have h1 : (2 * n + 1) % 2 = 1 := by omega
            have h2 : (2 * n + 1) / 2 = n := by omega
            simp only [h1, h2, Nat.one_ne_zero, if_neg, if_false]
            rw [hn, Sym2.eq_swap]
            exact star_mem_edgeSet G y x hadj.symm
          · have hmem : s(x, y) ∈ G0.edgeSet := by
              rw [hG0, SimpleGraph.edgeSet_fromEdgeSet]
              refine ⟨⟨he, ?_⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩
              intro w hw
              rcases Sym2.mem_iff.mp hw with rfl | rfl
              · exact hxS
              · exact hyS
            obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hHcov hmem)
            refine Set.mem_iUnion.mpr ⟨2 * n, ?_⟩
            have h1 : (2 * n) % 2 = 0 := by omega
            have h2 : (2 * n) / 2 = n := by omega
            simp only [h1, h2, if_pos]
            exact hn

end Erdos595Apex

theorem msl_erdos595_countable_deletion_2026_09_05 {V : Type*} (G : SimpleGraph V) (S : Set V) (hS : S.Countable) (hrest : Erdos595Apex.Coverable (SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → x ∉ S})) : Erdos595Apex.Coverable G := by exact Erdos595Apex.coverable_of_countable_deletion G S hS hrest
