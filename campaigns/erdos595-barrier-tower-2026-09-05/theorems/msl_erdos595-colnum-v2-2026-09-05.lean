import Mathlib

set_option autoImplicit false

namespace Erdos595Col

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

theorem colouring_cover (G : SimpleGraph V) (c : Sym2 V → ℕ)
    (hc : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
      ¬ (c s(x, y) = c s(y, z) ∧ c s(x, z) = c s(y, z))) : Coverable G := by
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

variable [LinearOrder V]

noncomputable def backCol (f : V → V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => if x < y then f y x else f x y, by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, asymm h]
    · simp [h]
    · simp [h, asymm h]⟩

theorem backCol_lt (f : V → V → ℕ) (a b : V) (h : a < b) :
    backCol f s(a, b) = f b a := by
  simp [backCol, Sym2.lift_mk, h]

theorem backCol_gt (f : V → V → ℕ) (a b : V) (h : b < a) :
    backCol f s(a, b) = f a b := by
  simp [backCol, Sym2.lift_mk, asymm h]

theorem coverable_of_backDegree (G : SimpleGraph V) (f : V → V → ℕ)
    (hf : ∀ v a b : V, a < v → b < v → f v a = f v b → a = b) : Coverable G := by
  classical
  refine colouring_cover G (backCol f) ?_
  rintro x y z hxy hyz hxz ⟨h1, h2⟩
  have hxyne : x ≠ y := hxy.ne
  have hyzne : y ≠ z := hyz.ne
  have hxzne : x ≠ z := hxz.ne
  rcases lt_trichotomy x y with hA | hA | hA
  · rcases lt_trichotomy y z with hB | hB | hB
    · have hxz' : x < z := hA.trans hB
      rw [backCol_lt f x z hxz', backCol_lt f y z hB] at h2
      exact hxyne (hf z x y hxz' hB h2)
    · exact hyzne hB
    · rw [backCol_lt f x y hA, backCol_gt f y z hB] at h1
      exact hxzne (hf y x z hA hB h1)
  · exact hxyne hA
  · rcases lt_trichotomy x z with hB | hB | hB
    · have hyz' : y < z := hA.trans hB
      rw [backCol_lt f x z hB, backCol_lt f y z hyz'] at h2
      exact hxyne (hf z x y hB hyz' h2)
    · exact hxzne hB
    · rw [backCol_gt f x y hA] at h1
      rw [backCol_gt f x z hB] at h2
      exact hyzne (hf x y z hA hB (h1.trans h2.symm))

end Erdos595Col

theorem msl_erdos595_colnum_v2_2026_09_05 {V : Type*} [LinearOrder V] (G : SimpleGraph V) (f : V → V → ℕ) (hf : ∀ v a b : V, a < v → b < v → f v a = f v b → a = b) : Erdos595Col.Coverable G := by exact Erdos595Col.coverable_of_backDegree G f hf
