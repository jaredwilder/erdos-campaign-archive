import Mathlib

set_option autoImplicit false

namespace Erdos595Mono

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

theorem cliqueFree_three_of_le {A B : SimpleGraph V} (hle : A ≤ B)
    (hB : B.CliqueFree 3) : A.CliqueFree 3 := by
  rw [cliqueFree_three_iff] at hB ⊢
  intro x y z hxy hyz hxz
  exact hB x y z (hle hxy) (hle hyz) (hle hxz)

theorem coverable_of_le (G K : SimpleGraph V) (hle : K ≤ G) (hG : Coverable G) :
    Coverable K := by
  classical
  obtain ⟨H, hHle, hHfree, hHcov⟩ := hG
  refine ⟨fun n => H n ⊓ K, ?_, ?_, ?_⟩
  · intro n x y h
    exact h.2
  · intro n
    exact cliqueFree_three_of_le (by intro x y h; exact h.1) (hHfree n)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hKadj : K.Adj x y := K.mem_edgeSet.mp he
      have hGmem : s(x, y) ∈ G.edgeSet := G.mem_edgeSet.mpr (hle hKadj)
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hHcov hGmem)
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      exact (H n ⊓ K).mem_edgeSet.mpr ⟨(H n).mem_edgeSet.mp hn, hKadj⟩

end Erdos595Mono

theorem msl_erdos595_coverable_mono_2026_09_05 {V : Type*} (G : SimpleGraph V) (K : SimpleGraph V) (hle : K ≤ G) (hG : Erdos595Mono.Coverable G) : Erdos595Mono.Coverable K := by exact Erdos595Mono.coverable_of_le G K hle hG
