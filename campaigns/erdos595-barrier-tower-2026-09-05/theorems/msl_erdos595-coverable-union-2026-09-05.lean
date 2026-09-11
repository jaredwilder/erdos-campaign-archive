import Mathlib

set_option autoImplicit false

namespace Erdos595Union

variable {V : Type*}

def Coverable (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧
    G.edgeSet ⊆ ⋃ n, (H n).edgeSet

theorem coverable_iUnion (G : SimpleGraph V) (K : ℕ → SimpleGraph V)
    (hle : ∀ n, K n ≤ G) (hcov : ∀ n, Coverable (K n))
    (hunion : G.edgeSet ⊆ ⋃ n, (K n).edgeSet) : Coverable G := by
  classical
  choose H hH using hcov
  refine ⟨fun m => H (Nat.unpair m).1 (Nat.unpair m).2, ?_, ?_, ?_⟩
  · intro m
    exact le_trans ((hH (Nat.unpair m).1).1 (Nat.unpair m).2) (hle _)
  · intro m
    exact (hH (Nat.unpair m).1).2.1 (Nat.unpair m).2
  · intro e he
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hunion he)
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ((hH n).2.2 hn)
    refine Set.mem_iUnion.mpr ⟨Nat.pair n k, ?_⟩
    simpa [Nat.unpair_pair] using hk

theorem coverable_sup (G G1 G2 : SimpleGraph V) (h1 : G1 ≤ G) (h2 : G2 ≤ G)
    (hc1 : Coverable G1) (hc2 : Coverable G2)
    (hunion : G.edgeSet ⊆ G1.edgeSet ∪ G2.edgeSet) : Coverable G := by
  classical
  refine coverable_iUnion G (fun n => if n = 0 then G1 else G2) ?_ ?_ ?_
  · intro n
    by_cases hn : n = 0 <;> simp [hn, h1, h2]
  · intro n
    by_cases hn : n = 0 <;> simp [hn, hc1, hc2]
  · intro e he
    rcases hunion he with h | h
    · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩

end Erdos595Union

theorem msl_erdos595_coverable_union_2026_09_05 {V : Type*} (G : SimpleGraph V) (K : ℕ → SimpleGraph V) (hle : ∀ n, K n ≤ G) (hcov : ∀ n, Erdos595Union.Coverable (K n)) (hunion : G.edgeSet ⊆ ⋃ n, (K n).edgeSet) : Erdos595Union.Coverable G := by exact Erdos595Union.coverable_iUnion G K hle hcov hunion
