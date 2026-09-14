import Mathlib

/-!
# JSPACE SHOT 2 — adjudication in the kernel.

Setting: a tournament `T`, and for `A ⊆ V`,
  `D(A) = {v : v → a for every a ∈ A}`.
Hypothesis `Schutte T k` : every `A` with `|A| ≤ k` has `D(A) ≠ ∅`.
(This is exactly `γ(T) > k`.)

* `noncollapse`  — the shot's equation (1). **TRUE**, proved here in general.
* `Fmom_le_Emom` — the second reciprocal moment is **never larger** than the first.
* `eq10_false`, `eq14_false`, `eq18_false` — (8)/(10), (14)/(16) and (18) are **FALSE**,
  witnessed by the 3-cycle at `k = 1`, which satisfies the hypothesis.
-/

namespace JSpaceShot2

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

/-- `D(A) = {v : v beats every element of A}`. `v ∉ A` is automatic by irreflexivity. -/
def Dset (T : Tournament V) (A : Finset V) : Finset V :=
  univ.filter (fun v => ∀ a ∈ A, T.beats v a)

/-- `γ(T) > k`, stated as: every set of size `≤ k` has a common dominator. -/
def Schutte (T : Tournament V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A.card ≤ k → (Dset T A).Nonempty

/-- **Equation (1) of Shot 2 — the non-collapse invariant. TRUE.** -/
theorem noncollapse {T : Tournament V} {k : ℕ} (h : Schutte T k)
    (A : Finset V) (hA : A.card ≤ k) : k + 1 ≤ A.card + (Dset T A).card := by
  by_contra hc
  push_neg at hc
  have hB : (A ∪ Dset T A).card ≤ k := by
    have := Finset.card_union_le A (Dset T A)
    omega
  obtain ⟨v, hv⟩ := h _ hB
  have hv2 : ∀ b ∈ A ∪ Dset T A, T.beats v b := (mem_filter.mp hv).2
  have hvA : v ∈ Dset T A := by
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    intro a ha
    exact hv2 a (Finset.mem_union_left _ ha)
  exact T.irrefl v (hv2 v (Finset.mem_union_right _ hvA))

/-- At full size `|A| = k`, `D(A)` is nonempty. -/
theorem one_le_card_Dset {T : Tournament V} {k : ℕ} (h : Schutte T k)
    {A : Finset V} (hA : A.card = k) : 1 ≤ (Dset T A).card := by
  have := noncollapse h A (le_of_eq hA)
  omega

/-- `E_k(T) = Σ_{|A|=k} 1/|D(A)|`  (equation (4)). -/
def Emom (T : Tournament V) (k : ℕ) : ℚ :=
  ∑ A ∈ powersetCard k (univ : Finset V), (1 : ℚ) / ((Dset T A).card : ℚ)

/-- `F_k(T) = Σ_{|A|=k} 1/|D(A)|²`  (equation (11)). -/
def Fmom (T : Tournament V) (k : ℕ) : ℚ :=
  ∑ A ∈ powersetCard k (univ : Finset V), (1 : ℚ) / ((Dset T A).card : ℚ) ^ 2

/-- **THE STRUCTURAL KILL.** `F_k(T) ≤ E_k(T)` always. -/
theorem Fmom_le_Emom {T : Tournament V} {k : ℕ} (h : Schutte T k) :
    Fmom T k ≤ Emom T k := by
  refine Finset.sum_le_sum ?_
  intro A hA
  have hAk : A.card = k := (mem_powersetCard.mp hA).2
  have h1 : 1 ≤ (Dset T A).card := one_le_card_Dset h hAk
  have hq : (1 : ℚ) ≤ ((Dset T A).card : ℚ) := by exact_mod_cast h1
  have hpos : (0 : ℚ) < ((Dset T A).card : ℚ) := lt_of_lt_of_le zero_lt_one hq
  have hsq : ((Dset T A).card : ℚ) ≤ ((Dset T A).card : ℚ) ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le hpos hsq

/-! ### The witness: the 3-cycle, `k = 1`. -/

/-- 3-cycle: `a → a+1`. -/
def C3 : Tournament (Fin 3) where
  beats a b := b = a + 1
  dec := inferInstance
  irrefl := by decide
  tot := by decide

theorem C3_schutte : Schutte C3 1 := by
  show ∀ A : Finset (Fin 3), A.card ≤ 1 → (Dset C3 A).Nonempty
  decide

theorem C3_all_D_card_one :
    ∀ A ∈ powersetCard 1 (univ : Finset (Fin 3)), (Dset C3 A).card = 1 := by decide

theorem C3_Emom : Emom C3 1 = 3 := by
  have hE : Emom C3 1 = ∑ _A ∈ powersetCard 1 (univ : Finset (Fin 3)), (1 : ℚ) := by
    refine Finset.sum_congr rfl ?_
    intro A hA
    rw [C3_all_D_card_one A hA]
    norm_num
  rw [hE, Finset.sum_const, Finset.card_powersetCard]
  simp

theorem C3_Fmom : Fmom C3 1 = 3 := by
  have hF : Fmom C3 1 = ∑ _A ∈ powersetCard 1 (univ : Finset (Fin 3)), (1 : ℚ) := by
    refine Finset.sum_congr rfl ?_
    intro A hA
    rw [C3_all_D_card_one A hA]
    norm_num
  rw [hF, Finset.sum_const, Finset.card_powersetCard]
  simp

/-- **Equation (8)/(10) is FALSE.** Claim `E_k ≥ C(N,k)(k+1)2^k/N` reads `3 ≥ 4`. -/
theorem eq10_false :
    ¬ (Emom C3 1 ≥ (Nat.choose 3 1 : ℚ) * ((1 + 1) * 2 ^ 1) / 3) := by
  rw [C3_Emom]; norm_num

/-- **Equation (14)/(16) is FALSE.** Claim `F_k ≥ C(N,k)(k+1)²2^k/N` reads `3 ≥ 8`. -/
theorem eq14_false :
    ¬ (Fmom C3 1 ≥ (Nat.choose 3 1 : ℚ) * ((1 + 1) ^ 2 * 2 ^ 1) / 3) := by
  rw [C3_Fmom]; norm_num

/-- **Equation (18) is FALSE.** `N ≥ (k+1)²2^k` would force `3 ≥ 8`. -/
theorem eq18_false : Schutte C3 1 ∧ Fintype.card (Fin 3) < (1 + 1) ^ 2 * 2 ^ 1 :=
  ⟨C3_schutte, by decide⟩

end JSpaceShot2

#print axioms JSpaceShot2.noncollapse
#print axioms JSpaceShot2.Fmom_le_Emom
#print axioms JSpaceShot2.eq14_false
