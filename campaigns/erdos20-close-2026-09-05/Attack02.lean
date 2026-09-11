/-
Erdős Problem 20 — the Sunflower Conjecture.

ATTACK 02: transfer of the Erdős–Rado sunflower lemma (Attack01) to the EXACT
statement left as `sorry` in the DeepMind formal-conjectures corpus file
`FormalConjectures/ErdosProblems/20.lean`, namely

    erdos_20.variants.erdos_rado_bound :
      ∀ n k, n > 0 → 2 ≤ k → f n k ≤ (k - 1) ^ n * n.factorial + 1

with `f`, `IsSunflower`, `IsSunflowerWithKernel` reproduced VERBATIM from the
corpus (`f` from ErdosProblems/20.lean, the sunflower predicates from
FormalConjecturesForMathlib/Combinatorics/SetFamily/Sunflower.lean), so that the
object proved about is the corpus object, not a convenient restatement.
-/
import Mathlib
import Attack01

namespace Erdos20Corpus

open Finset

/-! ### Corpus definitions, reproduced verbatim -/

/-- VERBATIM from FormalConjecturesForMathlib/Combinatorics/SetFamily/Sunflower.lean. -/
def IsSunflowerWithKernel {α : Type*} (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

/-- VERBATIM from FormalConjecturesForMathlib/Combinatorics/SetFamily/Sunflower.lean. -/
def IsSunflower {α : Type*} (F : Set (Set α)) : Prop := ∃ S, IsSunflowerWithKernel F S

/-- VERBATIM from FormalConjectures/ErdosProblems/20.lean.
`f n k` is minimal such that every family of `n`-uniform sets of size at least
`f n k` contains a `k`-sunflower. -/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

/-! ### The membership witness -/

theorem erdos_rado_mem (n k : ℕ) (hn : 0 < n) :
    ∀ {α : Type}, ∀ (F : Set (Set α)),
      ((∀ A ∈ F, A.ncard = n) ∧ ((k - 1) ^ n * n.factorial + 1) ≤ F.ncard) →
      ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S := by
  intro α F hFF
  obtain ⟨huni, hcard⟩ := hFF
  classical
  have hM1 : 1 ≤ F.ncard :=
    le_trans (Nat.le_add_left 1 ((k - 1) ^ n * n.factorial)) hcard
  have hFfin : F.Finite := by
    by_contra hinf
    have h0 := Set.Infinite.ncard hinf
    omega
  have hAfin : ∀ A ∈ F, A.Finite := by
    intro A hA
    by_contra hinf
    have h0 := Set.Infinite.ncard hinf
    have h1 := huni A hA
    omega
  -- total finitisation map
  have htf : ∀ A ∈ F,
      (((if h : A.Finite then h.toFinset else ∅) : Finset α) : Set α) = A := by
    intro A hA
    rw [dif_pos (hAfin A hA)]
    exact Set.Finite.coe_toFinset _
  have hmemF : ∀ A ∈ hFfin.toFinset, A ∈ F := fun A hA => (Set.Finite.mem_toFinset _).mp hA
  have hinjOn : Set.InjOn (fun A : Set α => if h : A.Finite then h.toFinset else ∅)
      (↑hFfin.toFinset : Set (Set α)) := by
    intro A hA B hB hAB
    have hA' := hmemF A (Finset.mem_coe.mp hA)
    have hB' := hmemF B (Finset.mem_coe.mp hB)
    simp only at hAB
    rw [← htf A hA', ← htf B hB', hAB]
  have hFscard :
      (hFfin.toFinset.image (fun A : Set α => if h : A.Finite then h.toFinset else ∅)).card
        = F.ncard := by
    rw [Finset.card_image_of_injOn hinjOn]
    exact (Set.ncard_eq_toFinset_card F hFfin).symm
  have hFsn : ∀ B ∈ hFfin.toFinset.image
      (fun A : Set α => if h : A.Finite then h.toFinset else ∅), B.card = n := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    have hA' := hmemF A hA
    rw [← Set.ncard_coe_finset, htf A hA', huni A hA']
  have hlt : (k - 1) ^ n * n.factorial <
      (hFfin.toFinset.image (fun A : Set α => if h : A.Finite then h.toFinset else ∅)).card := by
    rw [hFscard]
    exact Nat.lt_of_succ_le hcard
  obtain ⟨S, hSFs, hScard, C, hC⟩ :=
    Erdos20Attack.sunflower_lemma k n
      (hFfin.toFinset.image (fun A : Set α => if h : A.Finite then h.toFinset else ∅))
      hFsn hlt
  refine ⟨(fun B : Finset α => (↑B : Set α)) '' (↑S : Set (Finset α)), ?_, ?_,
    ⟨(↑C : Set α), ?_⟩⟩
  · rintro A ⟨B, hB, rfl⟩
    obtain ⟨A', hA', hA'B⟩ := Finset.mem_image.mp (hSFs (Finset.mem_coe.mp hB))
    have key : ((if h : A'.Finite then h.toFinset else ∅ : Finset α) : Set α) ∈ F := by
      rw [htf A' (hmemF A' hA')]
      exact hmemF A' hA'
    rw [hA'B] at key
    exact key
  · rw [Set.InjOn.ncard_image, Set.ncard_coe_finset, hScard]
    intro B₁ _ B₂ _ h
    exact Finset.coe_injective h
  · intro A hA B hB hAB
    obtain ⟨B₁, hB₁, rfl⟩ := hA
    obtain ⟨B₂, hB₂, rfl⟩ := hB
    have hne : B₁ ≠ B₂ := by rintro rfl; exact hAB rfl
    rw [← Finset.coe_inter,
      hC B₁ (Finset.mem_coe.mp hB₁) B₂ (Finset.mem_coe.mp hB₂) hne]

/-! ### The corpus theorem -/

/--
**Erdős–Rado (1960).** `f n k ≤ (k-1)^n * n! + 1`.
This is `erdos_20.variants.erdos_rado_bound` from the DeepMind formal-conjectures
corpus, where it stands as `sorry`.
-/
theorem erdos_rado_bound :
    ∀ n k, n > 0 → 2 ≤ k → f n k ≤ (k - 1) ^ n * n.factorial + 1 := by
  intro n k hn _
  exact Nat.sInf_le (erdos_rado_mem n k hn)

end Erdos20Corpus

#print axioms Erdos20Attack.sunflower_lemma
#print axioms Erdos20Corpus.erdos_rado_mem
#print axioms Erdos20Corpus.erdos_rado_bound
