import Mathlib

set_option autoImplicit false

namespace Erdos595Probe

variable {V : Type*}

theorem support_countable (S : Set (Sym2 V)) (hS : S.Countable) :
    (⋃ e ∈ S, {v : V | v ∈ e}).Countable := by
  refine hS.biUnion fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab : {v : V | v ∈ s(a, b)} = {a, b} := by
      ext v
      simp [Sym2.mem_iff]
    rw [hab]
    exact (Set.toFinite _).countable

theorem exists_free_triangle (hV : ¬ (Set.univ : Set V).Countable) (S : Set (Sym2 V))
    (hS : S.Countable) :
    ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      s(x, y) ∉ S ∧ s(y, z) ∉ S ∧ s(x, z) ∉ S := by
  classical
  set W : Set V := ⋃ e ∈ S, {v : V | v ∈ e} with hW
  have hWc : W.Countable := support_countable S hS
  have hinf : (Wᶜ).Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    apply hV
    have huniv : (Set.univ : Set V) = W ∪ Wᶜ := (Set.union_compl_self W).symm
    rw [huniv]
    exact hWc.union hfin.countable
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq 3
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hTcard
  have hxW : x ∉ W := by
    have : x ∈ Wᶜ := hTsub (by rw [hset]; simp)
    exact this
  have hyW : y ∉ W := by
    have : y ∈ Wᶜ := hTsub (by rw [hset]; simp)
    exact this
  have hzW : z ∉ W := by
    have : z ∈ Wᶜ := hTsub (by rw [hset]; simp)
    exact this
  have key : ∀ a b : V, a ∉ W → s(a, b) ∉ S := by
    intro a b ha hmem
    apply ha
    rw [hW]
    exact Set.mem_biUnion hmem (by simp [Sym2.mem_iff])
  exact ⟨x, y, z, hxy, hyz, hxz, key x y hxW, key y z hyW, key x z hxW⟩

end Erdos595Probe

theorem msl_erdos595_transversal_probe_2026_09_05 {V : Type*} (hV : ¬ (Set.univ : Set V).Countable) (S : Set (Sym2 V)) (hS : S.Countable) : ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ s(x, y) ∉ S ∧ s(y, z) ∉ S ∧ s(x, z) ∉ S := by exact Erdos595Probe.exists_free_triangle hV S hS
