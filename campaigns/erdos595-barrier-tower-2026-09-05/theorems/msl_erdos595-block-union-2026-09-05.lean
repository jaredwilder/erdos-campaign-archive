import Mathlib

set_option autoImplicit false

namespace Erdos595Blk

variable {V I : Type*}

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

theorem coverable_of_blocks (G : SimpleGraph V) (p : V → I)
    (K : I → ℕ → SimpleGraph V)
    (hle : ∀ i n, K i n ≤ G)
    (hfree : ∀ i n, (K i n).CliqueFree 3)
    (hblock : ∀ i n x y, (K i n).Adj x y → p x = i)
    (hcov : ∀ x y : V, G.Adj x y → ∃ n, (K (p x) n).Adj x y)
    (hGblock : ∀ x y : V, G.Adj x y → p x = p y) : Coverable G := by
  classical
  refine ⟨fun n => SimpleGraph.fromEdgeSet (⋃ i, (K i n).edgeSet), ?_, ?_, ?_⟩
  · intro n x y h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h.1
    exact hle i n ((K i n).mem_edgeSet.mp hi)
  · intro n
    rw [cliqueFree_three_iff]
    intro x y z hxy hyz hxz
    rw [SimpleGraph.fromEdgeSet_adj] at hxy hyz hxz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxy.1
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hyz.1
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxz.1
    have ai : (K i n).Adj x y := (K i n).mem_edgeSet.mp hi
    have aj : (K j n).Adj y z := (K j n).mem_edgeSet.mp hj
    have ak : (K k n).Adj x z := (K k n).mem_edgeSet.mp hk
    have e1 : p x = i := hblock i n x y ai
    have e2 : p y = j := hblock j n y z aj
    have e3 : p x = k := hblock k n x z ak
    have e4 : p x = p y := hGblock x y (hle i n ai)
    have hij : i = j := by rw [← e1, e4, e2]
    have hik : i = k := by rw [← e1, e3]
    subst hij
    subst hik
    exact (cliqueFree_three_iff (K i n)).mp (hfree i n) x y z ai aj ak
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hGadj : G.Adj x y := G.mem_edgeSet.mp he
      obtain ⟨n, hn⟩ := hcov x y hGadj
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      refine ⟨Set.mem_iUnion.mpr ⟨p x, (K (p x) n).mem_edgeSet.mpr hn⟩, ?_⟩
      exact fun hd => (G.not_isDiag_of_mem_edgeSet he) hd

end Erdos595Blk

theorem msl_erdos595_block_union_2026_09_05 {V I : Type*} (G : SimpleGraph V) (p : V → I) (K : I → ℕ → SimpleGraph V) (hle : ∀ i n, K i n ≤ G) (hfree : ∀ i n, (K i n).CliqueFree 3) (hblock : ∀ i n x y, (K i n).Adj x y → p x = i) (hcov : ∀ x y : V, G.Adj x y → ∃ n, (K (p x) n).Adj x y) (hGblock : ∀ x y : V, G.Adj x y → p x = p y) : Erdos595Blk.Coverable G := by exact Erdos595Blk.coverable_of_blocks G p K hle hfree hblock hcov hGblock
