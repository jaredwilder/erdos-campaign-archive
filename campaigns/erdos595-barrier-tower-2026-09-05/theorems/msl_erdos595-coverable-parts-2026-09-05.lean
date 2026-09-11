import Mathlib

set_option autoImplicit false

namespace Erdos595CP

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
  refine ⟨fun n => H n ⊓ K, fun n x y h => h.2, ?_, ?_⟩
  · intro n
    exact cliqueFree_three_of_le (by intro x y h; exact h.1) (hHfree n)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hKadj : K.Adj x y := K.mem_edgeSet.mp he
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hHcov (G.mem_edgeSet.mpr (hle hKadj)))
      exact Set.mem_iUnion.mpr ⟨n, (H n ⊓ K).mem_edgeSet.mpr ⟨(H n).mem_edgeSet.mp hn, hKadj⟩⟩

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

theorem pair_inj (a b x y : ℕ) (h : Nat.pair a b = Nat.pair x y) : a = x ∧ b = y := by
  have h2 := congrArg Nat.unpair h
  simp only [Nat.unpair_pair] at h2
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

noncomputable def partCol (p : V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => Nat.pair (min (p x) (p y)) (max (p x) (p y)), by
    intro x y
    simp [min_comm, max_comm]⟩

theorem partCol_mk (p : V → ℕ) (x y : V) :
    partCol p s(x, y) = Nat.pair (min (p x) (p y)) (max (p x) (p y)) := by
  simp [partCol, Sym2.lift_mk]

theorem coverable_of_coverable_parts (G : SimpleGraph V) (p : V → ℕ)
    (hpart : ∀ n : ℕ,
      Coverable (SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ partCol p e = Nat.pair n n})) :
    Coverable G := by
  classical
  refine coverable_iUnion G
    (fun k => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ partCol p e = k}) ?_ ?_ ?_
  · intro k x y h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    exact G.mem_edgeSet.mp h.1.1
  · intro k
    by_cases hk : ∃ n : ℕ, k = Nat.pair n n
    · obtain ⟨n, rfl⟩ := hk
      exact hpart n
    · refine ⟨fun _ => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ partCol p e = k},
        fun _ => le_refl _, ?_, fun e he => Set.mem_iUnion.mpr ⟨0, he⟩⟩
      intro _
      rw [cliqueFree_three_iff]
      intro x y z hxy hyz hxz
      rw [SimpleGraph.fromEdgeSet_adj] at hxy hyz hxz
      have h1 : partCol p s(x, y) = partCol p s(y, z) := by
        rw [hxy.1.2, hyz.1.2]
      have h2 : partCol p s(x, z) = partCol p s(y, z) := by
        rw [hxz.1.2, hyz.1.2]
      rw [partCol_mk, partCol_mk] at h1
      rw [partCol_mk, partCol_mk] at h2
      obtain ⟨m1, M1⟩ := pair_inj _ _ _ _ h1
      obtain ⟨m2, M2⟩ := pair_inj _ _ _ _ h2
      have hxy' : p x = p y := by omega
      apply hk
      refine ⟨p x, ?_⟩
      rw [← hxy.1.2, partCol_mk, hxy']
      simp
  · intro e he
    exact Set.mem_iUnion.mpr ⟨partCol p e, by
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨⟨he, rfl⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩⟩

end Erdos595CP

theorem msl_erdos595_coverable_parts_2026_09_05 {V : Type*} (G : SimpleGraph V) (p : V → ℕ) (hpart : ∀ n : ℕ, Erdos595CP.Coverable (SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ Erdos595CP.partCol p e = Nat.pair n n})) : Erdos595CP.Coverable G := by exact Erdos595CP.coverable_of_coverable_parts G p hpart
