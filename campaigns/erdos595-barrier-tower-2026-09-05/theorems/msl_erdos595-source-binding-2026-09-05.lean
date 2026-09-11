import Mathlib

set_option autoImplicit false

namespace Erdos595Bind

variable {V : Type*}

def Coverable (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧
    G.edgeSet ⊆ ⋃ n, (H n).edgeSet

def CoverableSource (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ n, (H n).CliqueFree 3) ∧
    G.edgeSet = ⋃ n, (H n).edgeSet

theorem le_of_edgeSet_subset {A B : SimpleGraph V} (h : A.edgeSet ⊆ B.edgeSet) : A ≤ B := by
  intro x y hxy
  exact B.mem_edgeSet.mp (h (A.mem_edgeSet.mpr hxy))

theorem coverable_iff_source (G : SimpleGraph V) : Coverable G ↔ CoverableSource G := by
  constructor
  · rintro ⟨H, hle, hfree, hcov⟩
    refine ⟨H, hfree, ?_⟩
    apply Set.Subset.antisymm hcov
    intro e he
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
    exact SimpleGraph.edgeSet_mono (hle n) hn
  · rintro ⟨H, hfree, heq⟩
    refine ⟨H, ?_, hfree, ?_⟩
    · intro n
      apply le_of_edgeSet_subset
      rw [heq]
      exact Set.subset_iUnion (fun m => (H m).edgeSet) n
    · rw [heq]

end Erdos595Bind

theorem msl_erdos595_source_binding_2026_09_05 {V : Type*} (G : SimpleGraph V) : Erdos595Bind.Coverable G ↔ Erdos595Bind.CoverableSource G := by exact Erdos595Bind.coverable_iff_source G
