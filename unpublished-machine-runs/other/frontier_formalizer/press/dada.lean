import Mathlib

/-!
THE SECOND COMPOSED SENTENCE - "dada" - same night, different corner of mathematics.

Words from two independently certified formalizations over the shared type Finset N:
  E148.IsUnitFractionSolution  (erdos-148: k naturals >= 1 whose reciprocals sum to 1)
  E131.NonDividing             (erdos-131: no element divides the sum of any nonempty
                                subset of the others)
The composition also exercises PARAMETER SPECIALIZATION (the k of the unit-fraction word),
the second operator of the V0 press. Defs copied verbatim from their certified sources.
-/

noncomputable section
open scoped BigOperators
open scoped Classical

namespace E148

def IsUnitFractionSolution (k : ℕ) (s : Finset ℕ) : Prop :=
  s.card = k ∧
    (∀ n ∈ s, 1 ≤ n) ∧
    (Finset.sum s (fun n => (1 : ℚ) / n)) = 1

end E148

namespace E131

def NonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ s ∈ (A.erase a).powerset,
    s.Nonempty → ¬ a ∣ s.sum id

end E131

namespace Press

/-- The baby's second sentence: an Egyptian-fraction representation of 1 whose denominator
    set is non-dividing. -/
def Dada (k : ℕ) (s : Finset ℕ) : Prop :=
  E148.IsUnitFractionSolution k s ∧ E131.NonDividing s

/-- VENN CELL 1 - satisfiable: the singleton {1} represents 1 = 1/1 and is vacuously
    non-dividing (erasing its only element leaves nothing to divide). -/
theorem dada_holds : Dada 1 ({1} : Finset ℕ) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
  intro a ha s hs hne
  have : s ⊆ ({1} : Finset ℕ).erase a := Finset.mem_powerset.mp hs
  fin_cases ha
  simp only [Finset.erase_singleton, Finset.subset_empty] at this
  simp [this] at hne

/-- VENN CELL 2 - `NonDividing` is NOT redundant: {2, 3, 6} is the classic Egyptian
    representation 1/2 + 1/3 + 1/6 = 1, yet 2 divides the subset-sum 6. -/
theorem unitfrac_but_dividing :
    E148.IsUnitFractionSolution 3 ({2, 3, 6} : Finset ℕ) ∧
      ¬ E131.NonDividing ({2, 3, 6} : Finset ℕ) := by
  constructor
  · refine ⟨by norm_num, by norm_num, by norm_num⟩
  · intro h
    have h2 : (2 : ℕ) ∈ ({2, 3, 6} : Finset ℕ) := by norm_num
    have h6 : ({6} : Finset ℕ) ∈ (({2, 3, 6} : Finset ℕ).erase 2).powerset := by decide
    exact h 2 h2 {6} h6 (by norm_num) (by norm_num)

/-- VENN CELL 3 - `IsUnitFractionSolution` is NOT redundant: {2, 3} is non-dividing
    (2 does not divide 3, 3 does not divide 2) but 1/2 + 1/3 is not 1. -/
theorem nondividing_but_not_unitfrac :
    E131.NonDividing ({2, 3} : Finset ℕ) ∧
      ¬ E148.IsUnitFractionSolution 2 ({2, 3} : Finset ℕ) := by
  constructor
  · -- `decide` is blocked here by the `Classical` scoped instance; unfold by hand instead.
    intro a ha s hs hne
    have hsub := Finset.mem_powerset.mp hs
    -- evaluate both erases up front; DecidableEq (Finset N) is a real instance, so `decide`
    -- reduces here even under the scoped Classical shadow.
    have e2 : ({2, 3} : Finset ℕ).erase 2 = {3} := by decide
    have e3 : ({2, 3} : Finset ℕ).erase 3 = {2} := by decide
    fin_cases ha
    · -- a = 2: s is a nonempty subset of {3}, hence s = {3}, and 2 does not divide 3.
      rw [e2] at hsub
      rcases Finset.subset_singleton_iff.mp hsub with h0 | h1
      · exact absurd (h0 ▸ hne) (by simp)
      · subst h1; norm_num
    · -- a = 3: s is a nonempty subset of {2}, hence s = {2}, and 3 does not divide 2.
      rw [e3] at hsub
      rcases Finset.subset_singleton_iff.mp hsub with h0 | h1
      · exact absurd (h0 ▸ hne) (by simp)
      · subst h1; norm_num
  · intro h
    have := h.2.2
    norm_num at this

end Press

end
