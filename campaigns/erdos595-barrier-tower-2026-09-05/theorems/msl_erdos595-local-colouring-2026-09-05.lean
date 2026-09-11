import Mathlib

set_option autoImplicit false

namespace Erdos595Loc

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

noncomputable def backCol (g : V → V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => if x < y then g y x else g x y, by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, asymm h]
    · simp [h]
    · simp [h, asymm h]⟩

theorem backCol_lt (g : V → V → ℕ) (a b : V) (h : a < b) :
    backCol g s(a, b) = g b a := by
  simp [backCol, Sym2.lift_mk, h]

theorem backCol_gt (g : V → V → ℕ) (a b : V) (h : b < a) :
    backCol g s(a, b) = g a b := by
  simp [backCol, Sym2.lift_mk, asymm h]

theorem coverable_of_local_colouring (G : SimpleGraph V) (g : V → V → ℕ)
    (hg : ∀ v a b : V, a < v → b < v → G.Adj a v → G.Adj b v → G.Adj a b →
      g v a ≠ g v b) : Coverable G := by
  classical
  refine colouring_cover G (backCol g) ?_
  rintro x y z hxy hyz hxz ⟨h1, h2⟩
  rcases lt_trichotomy x y with hA | hA | hA
  · rcases lt_trichotomy y z with hB | hB | hB
    · have hxz' : x < z := hA.trans hB
      rw [backCol_lt g x z hxz', backCol_lt g y z hB] at h2
      exact hg z x y hxz' hB hxz hyz hxy h2
    · exact hyz.ne hB
    · rw [backCol_lt g x y hA, backCol_gt g y z hB] at h1
      exact hg y x z hA hB hxy hyz.symm hxz h1
  · exact hxy.ne hA
  · rcases lt_trichotomy x z with hB | hB | hB
    · have hyz' : y < z := hA.trans hB
      rw [backCol_lt g x z hB, backCol_lt g y z hyz'] at h2
      exact hg z x y hB hyz' hxz hyz hxy h2
    · exact hxz.ne hB
    · rw [backCol_gt g x y hA] at h1
      rw [backCol_gt g x z hB] at h2
      exact hg x y z hA hB hxy.symm hxz.symm hyz (h1.trans h2.symm)

end Erdos595Loc

theorem msl_erdos595_local_colouring_2026_09_05 {V : Type*} [LinearOrder V] (G : SimpleGraph V) (g : V → V → ℕ) (hg : ∀ v a b : V, a < v → b < v → G.Adj a v → G.Adj b v → G.Adj a b → g v a ≠ g v b) : Erdos595Loc.Coverable G := by exact Erdos595Loc.coverable_of_local_colouring G g hg
