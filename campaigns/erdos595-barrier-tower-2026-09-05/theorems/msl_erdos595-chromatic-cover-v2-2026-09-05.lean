import Mathlib

set_option autoImplicit false

namespace Erdos595Chrom

variable {V : Type*}

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

theorem colouring_cover (G : SimpleGraph V) (c : Sym2 V → ℕ)
    (hc : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
      ¬ (c s(x, y) = c s(y, z) ∧ c s(x, z) = c s(y, z))) :
    ∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧
      G.edgeSet ⊆ ⋃ n, (H n).edgeSet := by
  classical
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_, ?_⟩
  · intro n x y h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    exact G.mem_edgeSet.mp h.1.1
  · intro n
    rw [cliqueFree_three_iff]
    intro x y z hxy hyz hxz
    rw [SimpleGraph.fromEdgeSet_adj] at hxy hyz hxz
    exact hc x y z (G.mem_edgeSet.mp hxy.1.1) (G.mem_edgeSet.mp hyz.1.1)
      (G.mem_edgeSet.mp hxz.1.1)
      ⟨hxy.1.2.trans hyz.1.2.symm, hxz.1.2.trans hyz.1.2.symm⟩
  · intro e he
    refine Set.mem_iUnion.mpr ⟨c e, ?_⟩
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨he, rfl⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩

theorem pair_inj (a b x y : ℕ) (h : Nat.pair a b = Nat.pair x y) : a = x ∧ b = y := by
  have h2 := congrArg Nat.unpair h
  simp only [Nat.unpair_pair] at h2
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

def edgeCol (col : V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => Nat.pair (min (col x) (col y)) (max (col x) (col y)), by
    intro x y
    simp [min_comm, max_comm]⟩

theorem countable_chromatic_cover (G : SimpleGraph V) (col : V → ℕ)
    (hcol : ∀ x y : V, G.Adj x y → col x ≠ col y) :
    ∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧
      G.edgeSet ⊆ ⋃ n, (H n).edgeSet := by
  refine colouring_cover G (edgeCol col) ?_
  rintro x y z hxy hyz hxz ⟨h1, h2⟩
  simp only [edgeCol, Sym2.lift_mk] at h1 h2
  have hxy' := hcol x y hxy
  have hyz' := hcol y z hyz
  have hxz' := hcol x z hxz
  obtain ⟨p1, q1⟩ := pair_inj _ _ _ _ h1
  obtain ⟨p2, q2⟩ := pair_inj _ _ _ _ h2
  omega

end Erdos595Chrom

theorem msl_erdos595_chromatic_cover_v2_2026_09_05 {V : Type*} (G : SimpleGraph V) (col : V → ℕ) (hcol : ∀ x y : V, G.Adj x y → col x ≠ col y) : ∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧ G.edgeSet ⊆ ⋃ n, (H n).edgeSet := by exact Erdos595Chrom.countable_chromatic_cover G col hcol
