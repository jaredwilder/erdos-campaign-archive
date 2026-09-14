import Mathlib

/-!
THE THIRD SENTENCE - "gaga" - and the first one that GREW UP. 2026-08-31, ~3am.

Spoken by the operator's language cook (Downloads/"Oh, I have one..txt"), formalized here so the
kernel can pass judgment on every step of the story:

  WORD 1 (Egyptian fractions, Erdos-148 territory): reciprocals sum to exactly 1.
  WORD 2 (additive combinatorics): all subset sums distinct.
  SENTENCE: a five-element set speaking both words at once.
  WITNESS: the Sylvester numbers {2, 3, 7, 43, 1806} - superincreasing, telescoping to 1.
  SELF-READING: cell 2 = superincreasing but not summing to 1; cell 3 = the lovely
  {3,4,5,6,20} which sums to 1 while 3+6 = 4+5.
  THE GROWN-UP MOVE: rereading exposed "five" as an accidental constant -> generalize to all n.

No `open scoped Classical` in this file ON PURPOSE: every predicate is over N/Q with honest
Decidable instances, so `decide` computes instead of being shadowed (the trap that bit dada).
-/

namespace Press

/-- Word 1: the reciprocals of the elements sum to exactly 1. -/
def EgyptianOne (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 2 ≤ a) ∧ (Finset.sum A (fun a => (1 : ℚ) / a)) = 1

/-- Word 2: the subset-sum map is injective - no two different subsets share a sum. -/
def DistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powerset, ∀ T ∈ A.powerset, S.sum id = T.sum id → S = T

/-- The sentence: an n-element Egyptian representation of 1 with all subset sums distinct. -/
def Gaga (n : ℕ) (A : Finset ℕ) : Prop :=
  A.card = n ∧ EgyptianOne A ∧ DistinctSubsetSums A

def sylvester5 : Finset ℕ := {2, 3, 7, 43, 1806}

/-- VENN CELL 1 - the sentence is TRUE at n = 5: the Sylvester witness. -/
theorem gaga_holds : Gaga 5 sylvester5 := by
  refine ⟨by decide, ⟨by decide, by norm_num [sylvester5]⟩, ?_⟩
  unfold DistinctSubsetSums
  decide

/-- VENN CELL 2 - the Egyptian word is load-bearing: {2,5,11,23,47} is superincreasing
    (all subset sums distinct) yet its reciprocals do not sum to 1. -/
theorem distinct_but_not_egyptian :
    DistinctSubsetSums ({2, 5, 11, 23, 47} : Finset ℕ) ∧
      ¬ EgyptianOne ({2, 5, 11, 23, 47} : Finset ℕ) := by
  refine ⟨?_, ?_⟩
  · unfold DistinctSubsetSums
    decide
  · intro h
    have := h.2
    norm_num at this

/-- VENN CELL 3 - the subset-sum word is load-bearing: {3,4,5,6,20} speaks perfect
    Egyptian fraction (1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1) but 3 + 6 = 4 + 5. -/
theorem egyptian_but_colliding :
    EgyptianOne ({3, 4, 5, 6, 20} : Finset ℕ) ∧
      ¬ DistinctSubsetSums ({3, 4, 5, 6, 20} : Finset ℕ) := by
  constructor
  · exact ⟨by decide, by norm_num⟩
  · intro h
    have h36 : ({3, 6} : Finset ℕ) ∈ ({3, 4, 5, 6, 20} : Finset ℕ).powerset := by decide
    have h45 : ({4, 5} : Finset ℕ) ∈ ({3, 4, 5, 6, 20} : Finset ℕ).powerset := by decide
    have hEq : ({3, 6} : Finset ℕ).sum id = ({4, 5} : Finset ℕ).sum id := by decide
    have := h _ h36 _ h45 hEq
    exact absurd this (by decide)

/-- THE GROWN-UP SENTENCE - the speaker reread itself, caught "five" as an accidental
    constant, and generalized. The intended witness family is the Sylvester construction
    (s₁ = 2, sₖ₊₁ = 1 + ∏ sᵢ, close with the product): believed provable, NOT YET PROVED
    HERE - this is the speaker's next utterance, honestly marked. -/
def SpeakerConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ A : Finset ℕ, Gaga n A

/-- The COMPRESSED five-word witness the cook found on reread: same sentence, largest
    symbol 28 instead of 1806. Semantic utterance compression, kernel-sealed. -/
theorem gaga_holds_compressed : Gaga 5 ({2, 4, 7, 14, 28} : Finset ℕ) := by
  refine ⟨by decide, ⟨by decide, by norm_num⟩, ?_⟩
  unfold DistinctSubsetSums
  decide

/-- THE VERB. The algebraic engine of SPLIT: for d dividing x², one Egyptian word becomes
    two, truth preserved: 1/x = 1/(x+d) + 1/(x + x²/d). Proved, not asserted - this is a
    certified grammar production rule. -/
theorem split_identity (x d : ℚ) (hx : 0 < x) (hd : 0 < d) :
    1 / x = 1 / (x + d) + 1 / (x + x ^ 2 / d) := by
  have h1 : x ≠ 0 := ne_of_gt hx
  have h2 : d ≠ 0 := ne_of_gt hd
  have h3 : x + d ≠ 0 := by positivity
  have h4 : x + x ^ 2 / d ≠ 0 := by positivity
  field_simp
  ring

theorem speaker_next : SpeakerConjecture := by
  sorry

end Press
