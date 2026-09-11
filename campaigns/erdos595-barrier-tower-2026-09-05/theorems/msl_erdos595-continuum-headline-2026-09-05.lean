import Mathlib

set_option autoImplicit false

namespace Erdos595Cont

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

noncomputable def firstDiff (col : V → ℕ → Bool) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => sInf {n | col x n ≠ col y n}, by
    intro x y
    have hset : {n | col x n ≠ col y n} = {n | col y n ≠ col x n} :=
      Set.ext fun n => ne_comm
    exact congrArg sInf hset⟩

theorem firstDiff_spec (col : V → ℕ → Bool) (x y : V) (h : col x ≠ col y) :
    col x (firstDiff col s(x, y)) ≠ col y (firstDiff col s(x, y)) := by
  have hne : {n | col x n ≠ col y n}.Nonempty := by
    obtain ⟨n, hn⟩ := Function.ne_iff.mp h
    exact ⟨n, hn⟩
  have := Nat.sInf_mem hne
  simpa [firstDiff, Sym2.lift_mk] using this

theorem coverable_of_continuum_colouring (G : SimpleGraph V) (col : V → ℕ → Bool)
    (hcol : ∀ x y : V, G.Adj x y → col x ≠ col y) : Coverable G := by
  classical
  refine colouring_cover G (firstDiff col) ?_
  rintro x y z hxy hyz hxz ⟨h1, h2⟩
  have dxy := firstDiff_spec col x y (hcol x y hxy)
  have dyz := firstDiff_spec col y z (hcol y z hyz)
  have dxz := firstDiff_spec col x z (hcol x z hxz)
  rw [h1] at dxy
  rw [h2] at dxz
  set n := firstDiff col s(y, z) with hn
  rcases hb : col x n <;> rcases hc : col y n <;> rcases hd : col z n <;>
    simp_all



theorem coverable_of_injects_continuum (G : SimpleGraph V) (f : V → ℕ → Bool)
    (hf : Function.Injective f) : Coverable G := by
  refine coverable_of_continuum_colouring G f ?_
  intro x y hxy heq
  exact G.ne_of_adj hxy (hf heq)

end Erdos595Cont

theorem msl_erdos595_continuum_headline_2026_09_05 {V : Type*} (G : SimpleGraph V) (f : V → ℕ → Bool) (hf : Function.Injective f) : Erdos595Cont.Coverable G := by exact Erdos595Cont.coverable_of_injects_continuum G f hf
