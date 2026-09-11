import Mathlib

set_option autoImplicit false

namespace Erdos595Hom

variable {V W : Type*}

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

theorem coverable_of_hom (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hf : ∀ x y : V, G.Adj x y → H.Adj (f x) (f y)) (hH : Coverable H) : Coverable G := by
  classical
  obtain ⟨K, hKle, hKfree, hKcov⟩ := hH
  refine ⟨fun n => G ⊓ SimpleGraph.comap f (K n), ?_, ?_, ?_⟩
  · intro n x y h
    exact h.1
  · intro n
    rw [cliqueFree_three_iff]
    intro x y z hxy hyz hxz
    have a1 : (K n).Adj (f x) (f y) := hxy.2
    have a2 : (K n).Adj (f y) (f z) := hyz.2
    have a3 : (K n).Adj (f x) (f z) := hxz.2
    exact (cliqueFree_three_iff (K n)).mp (hKfree n) (f x) (f y) (f z) a1 a2 a3
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hGadj : G.Adj x y := G.mem_edgeSet.mp he
      have hHadj : H.Adj (f x) (f y) := hf x y hGadj
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hKcov (H.mem_edgeSet.mpr hHadj))
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      exact (G ⊓ SimpleGraph.comap f (K n)).mem_edgeSet.mpr
        ⟨hGadj, (K n).mem_edgeSet.mp hn⟩

end Erdos595Hom

theorem msl_erdos595_hom_pullback_2026_09_05 {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W) (hf : ∀ x y : V, G.Adj x y → H.Adj (f x) (f y)) (hH : Erdos595Hom.Coverable H) : Erdos595Hom.Coverable G := by exact Erdos595Hom.coverable_of_hom G H f hf hH
