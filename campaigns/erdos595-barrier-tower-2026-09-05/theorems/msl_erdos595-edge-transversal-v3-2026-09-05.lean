import Mathlib

set_option autoImplicit false

namespace Erdos595Edge

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

theorem single_edge_cliqueFree (e : Sym2 V) :
    (SimpleGraph.fromEdgeSet {e}).CliqueFree 3 := by
  rw [cliqueFree_three_iff]
  intro x y z hxy hyz hxz
  rw [SimpleGraph.fromEdgeSet_adj] at hxy hyz hxz
  have heq : s(x, y) = s(y, z) := by
    rw [hxy.1, hyz.1]
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact hxy.2 hx
  · exact hxz.2 hx

theorem coverable_of_countable_edge_transversal (G : SimpleGraph V) (S : Set (Sym2 V))
    (hS : S.Countable) (hSsub : S ⊆ G.edgeSet)
    (hhit : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
      s(x, y) ∈ S ∨ s(y, z) ∈ S ∨ s(x, z) ∈ S) : Coverable G := by
  classical
  set G0 : SimpleGraph V := SimpleGraph.fromEdgeSet (G.edgeSet \ S) with hG0
  have hG0le : G0 ≤ G := by
    intro x y h
    rw [hG0, SimpleGraph.fromEdgeSet_adj] at h
    exact G.mem_edgeSet.mp h.1.1
  have hG0free : G0.CliqueFree 3 := by
    rw [cliqueFree_three_iff]
    intro x y z hxy hyz hxz
    have hxy' := hxy
    have hyz' := hyz
    have hxz' := hxz
    rw [hG0, SimpleGraph.fromEdgeSet_adj] at hxy' hyz' hxz'
    rcases hhit x y z (hG0le hxy) (hG0le hyz) (hG0le hxz) with h | h | h
    · exact hxy'.1.2 h
    · exact hyz'.1.2 h
    · exact hxz'.1.2 h
  rcases Set.eq_empty_or_nonempty S with hemp | hne
  · refine ⟨fun _ => G0, fun n => hG0le, fun n => hG0free, ?_⟩
    intro e he
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    rw [hG0, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨he, ?_⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩
    rw [hemp]
    exact Set.notMem_empty e
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hne
    have hfmem : ∀ m, f m ∈ S := by
      intro m
      rw [hf]
      exact ⟨m, rfl⟩
    refine ⟨fun n => Nat.rec G0 (fun m _ => SimpleGraph.fromEdgeSet {f m}) n, ?_, ?_, ?_⟩
    · intro n
      cases n with
      | zero => exact hG0le
      | succ m =>
        intro x y h
        rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff] at h
        have hmem : s(x, y) ∈ G.edgeSet := by
          rw [h.1]
          exact hSsub (hfmem m)
        exact G.mem_edgeSet.mp hmem
    · intro n
      cases n with
      | zero => exact hG0free
      | succ m => exact single_edge_cliqueFree (f m)
    · intro e he
      by_cases heS : e ∈ S
      · obtain ⟨n, hn⟩ : ∃ n, f n = e := by
          have : e ∈ Set.range f := by rw [← hf]; exact heS
          exact this
        refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
        show e ∈ (SimpleGraph.fromEdgeSet {f n}).edgeSet
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨hn.symm, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩
      · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
        show e ∈ G0.edgeSet
        rw [hG0, SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨⟨he, heS⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩

end Erdos595Edge

theorem msl_erdos595_edge_transversal_v3_2026_09_05 {V : Type*} (G : SimpleGraph V) (S : Set (Sym2 V)) (hS : S.Countable) (hSsub : S ⊆ G.edgeSet) (hhit : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z → s(x, y) ∈ S ∨ s(y, z) ∈ S ∨ s(x, z) ∈ S) : Erdos595Edge.Coverable G := by exact Erdos595Edge.coverable_of_countable_edge_transversal G S hS hSsub hhit
