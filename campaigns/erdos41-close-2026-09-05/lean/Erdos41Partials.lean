/-
Erdős Problem 41 — campaign `erdos41-close-2026-09-05`.

Target (erdosproblems.com/41, $500, OPEN):
  Let A ⊆ ℕ be infinite with all triple sums a+b+c distinct (aside from trivial
  coincidences).  Is  liminf |A ∩ [1,N]| / N^(1/3) = 0 ?

This file banks the SORRY-FREE partial results this campaign established.
It compiles against Mathlib 919544d4 / Lean 4.31.0-rc1.

Contents
  §1  `NtupleCondition` — transcribed VERBATIM from the DeepMind
      formal-conjectures file `FormalConjectures/ErdosProblems/41.lean`.
  §2  `IsB3` — the *faithful* B₃ (Sidon-set-of-order-3) condition from the prose.
  §3  FAITHFULNESS: `IsB3 → NtupleCondition · 3`, and an explicit separating
      witness showing the converse FAILS.  Hence the corpus formalisation states
      a STRICTLY STRONGER theorem than Erdős's problem.
  §4  The counting bound (the load-bearing partial): `m.choose 3 ≤ 3N + 1`,
      and its cube form `(m-2)^3 ≤ 18N + 6`.
-/
import Mathlib

open Finset Set

namespace Erdos41Campaign

/-! ### §1  The corpus condition, verbatim -/

/-- Transcribed verbatim from `FormalConjectures/ErdosProblems/41.lean`.
Note this quantifies over `Finset`s of card `n`, i.e. over sets of `n` *distinct*
elements — it is NOT the multiset (`B_n`) condition. -/
def NtupleCondition {α : Type} [AddCommMonoid α] (A : Set α) (n : ℕ) : Prop :=
  ∀ (I : Finset α) (J : Finset α),
    ↑I ⊆ A ∧ ↑J ⊆ A ∧ I.card = n ∧ J.card = n ∧
    (∑ i ∈ I, i = ∑ j ∈ J, j) → I = J

/-! ### §2  The faithful B₃ condition -/

/-- The prose condition of Erdős 41: the triple sums `a+b+c` are all distinct
"aside from the trivial coincidences", i.e. `a+b+c = a'+b'+c'` forces the
*multisets* `{a,b,c}` and `{a',b',c'}` to agree.  Repetitions ARE allowed. -/
def IsB3 (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ a' ∈ A, ∀ b' ∈ A, ∀ c' ∈ A,
    a + b + c = a' + b' + c' → ({a, b, c} : Multiset ℕ) = {a', b', c'}

/-! ### §3  Faithfulness audit -/

/-- Every genuine B₃ set satisfies the corpus condition. -/
theorem isB3_imp_ntupleCondition (A : Set ℕ) (h : IsB3 A) : NtupleCondition A 3 := by
  rintro I J ⟨hIA, hJA, hI3, hJ3, hsum⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hI3
  obtain ⟨a', b', c', hab', hac', hbc', rfl⟩ := Finset.card_eq_three.mp hJ3
  have ha : a ∈ A := hIA (by simp)
  have hb : b ∈ A := hIA (by simp)
  have hc : c ∈ A := hIA (by simp)
  have ha' : a' ∈ A := hJA (by simp)
  have hb' : b' ∈ A := hJA (by simp)
  have hc' : c' ∈ A := hJA (by simp)
  have hs : a + b + c = a' + b' + c' := by
    simpa [Finset.sum_insert, Finset.mem_insert, hab, hac, hbc, hab', hac', hbc',
      add_assoc] using hsum
  have hms := h a ha b hb c hc a' ha' b' hb' c' hc' hs
  have := congrArg Multiset.toFinset hms
  simpa using this

/-- SEPARATING WITNESS.  `{1,2,3}` satisfies the corpus condition at `n = 3`
but is not a B₃ set: `1+1+3 = 1+2+2 = 5` while `{1,1,3} ≠ {1,2,2}` as multisets.
Together with `isB3_imp_ntupleCondition` this shows the hypothesis class of the
corpus statement STRICTLY CONTAINS the hypothesis class of Erdős 41, so the
corpus theorem `erdos_41` is strictly stronger than the problem it cites. -/
theorem ntupleCondition_not_isB3 :
    NtupleCondition ({1, 2, 3} : Set ℕ) 3 ∧ ¬ IsB3 ({1, 2, 3} : Set ℕ) := by
  constructor
  · rintro I J ⟨hIA, hJA, hI3, hJ3, -⟩
    have key : ∀ K : Finset ℕ, (↑K : Set ℕ) ⊆ ({1, 2, 3} : Set ℕ) → K.card = 3 →
        K = ({1, 2, 3} : Finset ℕ) := by
      intro K hK hcard
      have hsub : K ⊆ ({1, 2, 3} : Finset ℕ) := by
        intro x hx
        have hx' := hK (Finset.mem_coe.mpr hx)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hx'
      have h3 : ({1, 2, 3} : Finset ℕ).card = 3 := by decide
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [key I hIA hI3, key J hJA hJ3]
  · intro h
    have h1 : (1 : ℕ) ∈ ({1, 2, 3} : Set ℕ) := by simp
    have h2 : (2 : ℕ) ∈ ({1, 2, 3} : Set ℕ) := by simp
    have h3 : (3 : ℕ) ∈ ({1, 2, 3} : Set ℕ) := by simp
    have := h 1 h1 1 h1 3 h3 1 h1 2 h2 2 h2 (by norm_num)
    exact absurd this (by decide)

/-! ### §4  The counting bound -/

/-- THE LOAD-BEARING PARTIAL.  If `A` satisfies the (weak) corpus condition at
`n = 3`, then writing `m = |A ∩ [1,N]|` we have `C(m,3) ≤ 3N + 1`.

Proof: the sum map is injective on the 3-element subsets of `A ∩ [1,N]` and
lands in `[0, 3N]`.

Because `NtupleCondition` is implied by `IsB3` (§3), this bound holds a fortiori
for every genuine B₃ set. -/
theorem ntuple3_card_choose_le (A : Set ℕ) (h : NtupleCondition A 3) (N : ℕ) :
    ((A ∩ Set.Icc 1 N).ncard).choose 3 ≤ 3 * N + 1 := by
  classical
  set T : Finset ℕ := {x ∈ Finset.Icc 1 N | x ∈ A} with hTdef
  have hTmem : ∀ x, x ∈ T ↔ (x ∈ A ∧ 1 ≤ x ∧ x ≤ N) := by
    intro x
    simp only [hTdef, Finset.mem_filter, Finset.mem_Icc]
    tauto
  have hTcoe : (↑T : Set ℕ) = A ∩ Set.Icc 1 N := by
    ext x
    simp only [Finset.mem_coe, hTmem x, Set.mem_inter_iff, Set.mem_Icc]
    try tauto
  have hcard : (A ∩ Set.Icc 1 N).ncard = T.card := by
    rw [← hTcoe]; exact ncard_coe_finset T
  rw [hcard, ← Finset.card_powersetCard, ← Finset.card_range (3 * N + 1)]
  apply Finset.card_le_card_of_injOn (fun I => ∑ i ∈ I, i)
  · intro I hI
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hI
    obtain ⟨hsub, hc⟩ := hI
    simp only [Finset.mem_coe, Finset.mem_range]
    have hb : ∑ i ∈ I, i ≤ I.card * N := by
      calc ∑ i ∈ I, i ≤ ∑ _i ∈ I, N :=
            Finset.sum_le_sum (fun x hx => ((hTmem x).1 (hsub hx)).2.2)
        _ = I.card * N := by rw [Finset.sum_const, smul_eq_mul]
    rw [hc] at hb
    omega
  · intro I hI J hJ hEq
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hI hJ
    exact h I J ⟨fun x hx => ((hTmem x).1 (hI.1 (Finset.mem_coe.mp hx))).1,
                 fun x hx => ((hTmem x).1 (hJ.1 (Finset.mem_coe.mp hx))).1,
                 hI.2, hJ.2, hEq⟩

/-- Cube form of the counting bound: `(m-2)^3 ≤ 18N + 6`.
This is the precise sense in which `N^(1/3)` is the correct normalisation in
Erdős 41 — the ratio `|A ∩ [1,N]| / N^(1/3)` is BOUNDED, so the liminf in the
conjecture is a finite number and the only question is whether it is zero. -/
theorem ntuple3_cube_bound (A : Set ℕ) (h : NtupleCondition A 3) (N : ℕ) :
    ((A ∩ Set.Icc 1 N).ncard - 2) ^ 3 ≤ 18 * N + 6 := by
  set m := (A ∩ Set.Icc 1 N).ncard with hm
  have h1 : m.choose 3 ≤ 3 * N + 1 := ntuple3_card_choose_le A h N
  have h2 : 6 * m.choose 3 = m * (m - 1) * (m - 2) := by
    have hd := Nat.descFactorial_eq_factorial_mul_choose m 3
    simp [Nat.descFactorial, Nat.factorial] at hd
    rw [← hd]; ring
  have h3 : (m - 2) ^ 3 ≤ m * (m - 1) * (m - 2) := by
    calc (m - 2) ^ 3 = (m - 2) * (m - 2) * (m - 2) := by ring
      _ ≤ m * (m - 1) * (m - 2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  omega

/-! ### §5  Collapse to the pairwise condition -/

/-- For an INFINITE set, the corpus condition at `n = 3` already forces the
corpus condition at `n = 2`.

Proof: if `a + b = c + d` with `{a,b} ≠ {c,d}`, pick any `x ∈ A` outside all four
(possible because `A` is infinite); then `{a,b,x}` and `{c,d,x}` are distinct
3-element subsets of `A` with equal sums.

CONSEQUENCE.  The hypothesis of the corpus statement `erdos_41` implies the
hypothesis of the corpus statement `erdos_41.variants.pairwise` — which is
Erdős's SOLVED theorem.  So every `A` admissible for Erdős 41 already satisfies
`liminf |A ∩ [1,N]| / N^(1/2) = 0`.  The open content of Erdős 41 is exactly the
gap between the exponents `1/2` and `1/3`; no argument that only re-derives the
pairwise statement can close it. -/
theorem ntuple3_imp_ntuple2 (A : Set ℕ) (hinf : A.Infinite) (h : NtupleCondition A 3) :
    NtupleCondition A 2 := by
  classical
  rintro I J ⟨hIA, hJA, hI2, hJ2, hsum⟩
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hI2
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hJ2
  set U : Finset ℕ := ({a, b} : Finset ℕ) ∪ ({c, d} : Finset ℕ) with hU
  obtain ⟨x, hx⟩ := (hinf.diff U.finite_toSet).nonempty
  have hxA : x ∈ A := hx.1
  have hxU : x ∉ U := fun hc => hx.2 (Finset.mem_coe.mpr hc)
  have hxI : x ∉ ({a, b} : Finset ℕ) := fun hc => hxU (Finset.mem_union_left _ hc)
  have hxJ : x ∉ ({c, d} : Finset ℕ) := fun hc => hxU (Finset.mem_union_right _ hc)
  have hcI : (insert x ({a, b} : Finset ℕ)).card = 3 := by
    rw [Finset.card_insert_of_notMem hxI, hI2]
  have hcJ : (insert x ({c, d} : Finset ℕ)).card = 3 := by
    rw [Finset.card_insert_of_notMem hxJ, hJ2]
  have hsI : ∑ i ∈ insert x ({a, b} : Finset ℕ), i = x + ∑ i ∈ ({a, b} : Finset ℕ), i :=
    Finset.sum_insert hxI
  have hsJ : ∑ i ∈ insert x ({c, d} : Finset ℕ), i = x + ∑ i ∈ ({c, d} : Finset ℕ), i :=
    Finset.sum_insert hxJ
  have key := h (insert x ({a, b} : Finset ℕ)) (insert x ({c, d} : Finset ℕ))
    ⟨by
      intro y hy
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hy'
      · exact hxA
      · exact hIA (Finset.mem_coe.mpr hy'),
     by
      intro y hy
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hy'
      · exact hxA
      · exact hJA (Finset.mem_coe.mpr hy'),
     hcI, hcJ, by rw [hsI, hsJ, hsum]⟩
  have := congrArg (fun s => Finset.erase s x) key
  simpa [Finset.erase_insert hxI, Finset.erase_insert hxJ] using this

end Erdos41Campaign
