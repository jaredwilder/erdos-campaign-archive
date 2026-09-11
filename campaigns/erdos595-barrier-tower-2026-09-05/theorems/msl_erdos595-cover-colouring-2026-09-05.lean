import Mathlib

set_option autoImplicit false

namespace Erdos595Cover

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

theorem cover_iff_colouring (G : SimpleGraph V) :
    (∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧
        G.edgeSet ⊆ ⋃ n, (H n).edgeSet)
      ↔ (∃ c : Sym2 V → ℕ, ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
          ¬ (c s(x, y) = c s(y, z) ∧ c s(x, z) = c s(y, z))) := by
  classical
  constructor
  · rintro ⟨H, hle, hfree, hcov⟩
    refine ⟨fun e => if h : ∃ n, e ∈ (H n).edgeSet then Nat.find h else 0, ?_⟩
    set c : Sym2 V → ℕ := fun e => if h : ∃ n, e ∈ (H n).edgeSet then Nat.find h else 0 with hcdef
    have hmem : ∀ e ∈ G.edgeSet, e ∈ (H (c e)).edgeSet := by
      intro e he
      have hex : ∃ n, e ∈ (H n).edgeSet := by
        have := hcov he
        simpa using this
      simp only [hcdef, dif_pos hex]
      exact Nat.find_spec hex
    rintro x y z hxy hyz hxz ⟨h1, h2⟩
    have e1 : s(x, y) ∈ (H (c s(x, y))).edgeSet := hmem _ (G.mem_edgeSet.mpr hxy)
    have e2 : s(y, z) ∈ (H (c s(y, z))).edgeSet := hmem _ (G.mem_edgeSet.mpr hyz)
    have e3 : s(x, z) ∈ (H (c s(x, z))).edgeSet := hmem _ (G.mem_edgeSet.mpr hxz)
    rw [← h1] at e2
    rw [h2, ← h1] at e3
    exact (cliqueFree_three_iff (H (c s(x, y)))).mp (hfree _) x y z
      ((H (c s(x, y))).mem_edgeSet.mp e1) ((H (c s(x, y))).mem_edgeSet.mp e2)
      ((H (c s(x, y))).mem_edgeSet.mp e3)
  · rintro ⟨c, hc⟩
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

end Erdos595Cover

theorem msl_erdos595_cover_colouring_2026_09_05 {V : Type*} (G : SimpleGraph V) : (∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧ G.edgeSet ⊆ ⋃ n, (H n).edgeSet) ↔ (∃ c : Sym2 V → ℕ, ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z → ¬ (c s(x, y) = c s(y, z) ∧ c s(x, z) = c s(y, z))) := by exact Erdos595Cover.cover_iff_colouring G
