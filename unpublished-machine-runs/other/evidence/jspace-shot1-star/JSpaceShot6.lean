import Mathlib

/-! # JSPACE SHOT 6 — adjudication in the kernel. -/

namespace JSpaceShot6

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

def Dset (T : Tournament V) (A : Finset V) : Finset V :=
  univ.filter (fun v => ∀ a ∈ A, T.beats v a)

theorem mem_Dset {T : Tournament V} {A : Finset V} {v : V} :
    v ∈ Dset T A ↔ ∀ a ∈ A, T.beats v a := by simp [Dset]

/-- `S_k`: every set of size `≤ k` has a common dominator. -/
def HasS (T : Tournament V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A.card ≤ k → (Dset T A).Nonempty

theorem not_mem_of_mem_Dset {T : Tournament V} {A : Finset V} {v : V}
    (h : v ∈ Dset T A) : v ∉ A := fun hv => T.irrefl v (mem_Dset.mp h v hv)

/-! ## (1) — TRUE. The residual inherits the whole problem. -/

/-- **Equation (1) of Shot 6.**  If `B ⊆ D(A)` and `|A| + |B| ≤ k`, then `B` has a
dominator lying *inside* `D(A)`.  That is: `T[D(A)]` has `S_(k-|A|)`. -/
theorem residual_inherits {T : Tournament V} {k : ℕ} (h : HasS T k)
    (A B : Finset V) (hB : B ⊆ Dset T A) (hc : A.card + B.card ≤ k) :
    ∃ v ∈ Dset T A, v ∉ B ∧ ∀ b ∈ B, T.beats v b := by
  have hcard : (A ∪ B).card ≤ k := le_trans (Finset.card_union_le A B) hc
  obtain ⟨v, hv⟩ := h _ hcard
  have hvA : v ∈ Dset T A :=
    mem_Dset.mpr (fun a ha => mem_Dset.mp hv a (Finset.mem_union_left _ ha))
  have hvB : ∀ b ∈ B, T.beats v b :=
    fun b hb => mem_Dset.mp hv b (Finset.mem_union_right _ hb)
  exact ⟨v, hvA, fun hmem => T.irrefl v (hvB v hmem), hvB⟩

/-! ## (5) — TRUE. Source packing. -/

def Mlev (T : Tournament V) (r : ℕ) : ℕ :=
  ∑ A ∈ powersetCard r (univ : Finset V), (Dset T A).card

/-- **Equation (5) of Shot 6.**  `M_r ≤ C(N, r+1)`, because `(A,v) ↦ A ∪ {v}` is
injective: `v` is the unique source of the tournament induced on `A ∪ {v}`. -/
theorem Mlev_le (T : Tournament V) (r : ℕ) :
    Mlev T r ≤ Nat.choose (Fintype.card V) (r + 1) := by
  have hcard : Mlev T r =
      ((powersetCard r (univ : Finset V)).sigma (fun A => Dset T A)).card := by
    rw [Finset.card_sigma]
    rfl
  have htgt : Nat.choose (Fintype.card V) (r + 1)
      = (powersetCard (r + 1) (univ : Finset V)).card := by
    rw [Finset.card_powersetCard, Finset.card_univ]
  rw [hcard, htgt]
  refine Finset.card_le_card_of_injOn (fun p => insert p.2 p.1) ?_ ?_
  · rintro ⟨A, v⟩ hp
    rw [Finset.mem_coe, Finset.mem_sigma] at hp
    obtain ⟨hA, hv⟩ := hp
    rw [mem_powersetCard] at hA
    refine Finset.mem_coe.mpr (mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩)
    show (insert v A).card = r + 1
    rw [Finset.card_insert_of_notMem (not_mem_of_mem_Dset hv), hA.2]
  · rintro ⟨A, v⟩ hp ⟨A', v'⟩ hp' heq
    rw [Finset.mem_coe, Finset.mem_sigma] at hp hp'
    obtain ⟨-, hv⟩ := hp
    obtain ⟨-, hv'⟩ := hp'
    have hvA : v ∉ A := not_mem_of_mem_Dset hv
    have hvA' : v' ∉ A' := not_mem_of_mem_Dset hv'
    have heq' : insert v A = insert v' A' := heq
    -- v and v' are both sources of the same (r+1)-set, so they coincide
    have hveq : v = v' := by
      by_contra hne
      have hv_in : v ∈ insert v' A' := by rw [← heq']; exact Finset.mem_insert_self _ _
      have hv'_in : v' ∈ insert v A := by rw [heq']; exact Finset.mem_insert_self _ _
      have hvA'mem : v ∈ A' := by
        rcases Finset.mem_insert.mp hv_in with h | h
        · exact absurd h hne
        · exact h
      have hv'Amem : v' ∈ A := by
        rcases Finset.mem_insert.mp hv'_in with h | h
        · exact absurd h.symm hne
        · exact h
      have h1 : T.beats v' v := mem_Dset.mp hv' v hvA'mem
      have h2 : T.beats v v' := mem_Dset.mp hv v' hv'Amem
      exact ((T.tot v v' hne).mp h2) h1
    subst hveq
    have hAA : A = A' := by
      have h1 : (insert v A).erase v = A := Finset.erase_insert hvA
      have h2 : (insert v A').erase v = A' := Finset.erase_insert hvA'
      rw [← h1, ← h2, heq']
    subst hAA
    rfl

/-- **Equation (6) of Shot 6.**  If every `r`-set has at least `m` dominators then
`m · C(N,r) ≤ C(N,r+1)`.  This is the exact residual recursion. -/
theorem source_packing {T : Tournament V} {r m : ℕ}
    (hm : ∀ A ∈ powersetCard r (univ : Finset V), m ≤ (Dset T A).card) :
    m * Nat.choose (Fintype.card V) r ≤ Nat.choose (Fintype.card V) (r + 1) := by
  refine le_trans ?_ (Mlev_le T r)
  calc m * Nat.choose (Fintype.card V) r
      = ∑ _A ∈ powersetCard r (univ : Finset V), m := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul,
            Nat.mul_comm]
    _ ≤ Mlev T r := Finset.sum_le_sum hm

/-! ## (7)/(8) — FALSE.  The dyadic residual cube. -/

/-- `T4`: a 3-cycle `0→1→2→0` together with a sink `3` beaten by all of `0,1,2`. -/
def T4 : Tournament (Fin 4) where
  beats a b :=
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a ≠ 3 ∧ b = 3)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

/-- `T4` has `S_1`. -/
theorem T4_hasS : HasS T4 1 := by
  show ∀ A : Finset (Fin 4), A.card ≤ 1 → (Dset T4 A).Nonempty
  decide

/-- **(8) is FALSE.**  With `P = (3)` and signature `σ = (0)`, the cell
`C_σ(P) = {v ≠ 3 : ¬ v → 3}` is EMPTY, while (8) demands `|C_σ| ≥ f(0) = 1`. -/
theorem eq8_false :
    HasS T4 1 ∧
    ((univ : Finset (Fin 4)).filter (fun v => v ≠ 3 ∧ ¬ T4.beats v 3)) = ∅ :=
  ⟨T4_hasS, by decide⟩

/-! ## The justification offered for (7): vertex switching. -/

def switchAt (T : Tournament V) (p : V) : Tournament V where
  beats a b := if a = p then T.beats b a else if b = p then T.beats b a else T.beats a b
  dec := inferInstance
  irrefl := by
    intro a
    split_ifs <;> exact T.irrefl a
  tot := by
    intro a b hab
    split_ifs <;>
      first
        | exact T.tot b a (Ne.symm hab)
        | exact T.tot a b hab
        | simp_all

/-- Paley tournament on 7 vertices: `a → b` iff `b - a ∈ {1,2,4}`. -/
def P7 : Tournament (Fin 7) where
  beats a b := (b - a) = 1 ∨ (b - a) = 2 ∨ (b - a) = 4
  dec := inferInstance
  irrefl := by decide
  tot := by decide

set_option maxRecDepth 100000 in
theorem P7_hasS : HasS P7 2 := by
  show ∀ A : Finset (Fin 7), A.card ≤ 2 → (Dset P7 A).Nonempty
  decide

set_option maxRecDepth 100000 in
/-- **Vertex switching does NOT preserve `S_k`.**  `P7` has `S_2`;
switching at vertex `0` destroys it. -/
theorem switching_breaks_S : HasS P7 2 ∧ ¬ HasS (switchAt P7 0) 2 := by
  refine ⟨P7_hasS, ?_⟩
  show ¬ ∀ A : Finset (Fin 7), A.card ≤ 2 → (Dset (switchAt P7 0) A).Nonempty
  decide

end JSpaceShot6

#print axioms JSpaceShot6.residual_inherits
#print axioms JSpaceShot6.Mlev_le
#print axioms JSpaceShot6.source_packing
#print axioms JSpaceShot6.eq8_false
#print axioms JSpaceShot6.switching_breaks_S
