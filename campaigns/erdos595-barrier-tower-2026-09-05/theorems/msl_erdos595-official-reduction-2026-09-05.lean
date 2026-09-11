import Mathlib

set_option autoImplicit false

namespace Erdos595Off

variable {V : Type*}

def CoverableSource (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ n, (H n).CliqueFree 3) ∧ G.edgeSet = ⋃ n, (H n).edgeSet

def NoMonoTriangle (G : SimpleGraph V) (c : Sym2 V → ℕ) : Prop :=
  ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
    ¬ (c s(x, y) = c s(y, z) ∧ c s(x, z) = c s(y, z))

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

theorem le_of_edgeSet_subset {A B : SimpleGraph V} (h : A.edgeSet ⊆ B.edgeSet) : A ≤ B := by
  intro x y hxy
  exact B.mem_edgeSet.mp (h (A.mem_edgeSet.mpr hxy))

theorem official_reduction (G : SimpleGraph V) :
    CoverableSource G ↔ ∃ c : Sym2 V → ℕ, NoMonoTriangle G c := by
  classical
  constructor
  · rintro ⟨H, hfree, heq⟩
    have hle : ∀ n, H n ≤ G := by
      intro n
      apply le_of_edgeSet_subset
      rw [heq]
      exact Set.subset_iUnion (fun m => (H m).edgeSet) n
    have hmem : ∀ e ∈ G.edgeSet, ∃ n, e ∈ (H n).edgeSet := by
      intro e he
      rw [heq] at he
      exact Set.mem_iUnion.mp he
    refine ⟨fun e => if h : ∃ n, e ∈ (H n).edgeSet then Nat.find h else 0, ?_⟩
    set c : Sym2 V → ℕ := fun e => if h : ∃ n, e ∈ (H n).edgeSet then Nat.find h else 0
      with hcdef
    intro x y z hxy hyz hxz
    rintro ⟨h1, h2⟩
    have key : ∀ a b : V, G.Adj a b → s(a, b) ∈ (H (c s(a, b))).edgeSet := by
      intro a b hab
      have hex : ∃ n, s(a, b) ∈ (H n).edgeSet := hmem _ (G.mem_edgeSet.mpr hab)
      simp only [hcdef, dif_pos hex]
      exact Nat.find_spec hex
    have e1 := key x y hxy
    have e2 := key y z hyz
    have e3 := key x z hxz
    rw [← h1] at e2
    rw [h2, ← h1] at e3
    exact (cliqueFree_three_iff (H (c s(x, y)))).mp (hfree _) x y z
      ((H (c s(x, y))).mem_edgeSet.mp e1) ((H (c s(x, y))).mem_edgeSet.mp e2)
      ((H (c s(x, y))).mem_edgeSet.mp e3)
  · rintro ⟨c, hc⟩
    refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_⟩
    · intro n
      rw [cliqueFree_three_iff]
      intro x y z hxy hyz hxz
      rw [SimpleGraph.fromEdgeSet_adj] at hxy hyz hxz
      exact hc x y z (G.mem_edgeSet.mp hxy.1.1) (G.mem_edgeSet.mp hyz.1.1)
        (G.mem_edgeSet.mp hxz.1.1)
        ⟨hxy.1.2.trans hyz.1.2.symm, hxz.1.2.trans hyz.1.2.symm⟩
    · apply Set.Subset.antisymm
      · intro e he
        refine Set.mem_iUnion.mpr ⟨c e, ?_⟩
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨⟨he, rfl⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩
      · intro e he
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
        rw [SimpleGraph.edgeSet_fromEdgeSet] at hn
        exact hn.1.1

end Erdos595Off

theorem msl_erdos595_official_reduction_2026_09_05 {V : Type*} (G : SimpleGraph V) : Erdos595Off.CoverableSource G ↔ ∃ c : Sym2 V → ℕ, Erdos595Off.NoMonoTriangle G c := by exact Erdos595Off.official_reduction G
