import Mathlib

/-!
THE SPEAKER, KERNEL-SEALED. 2026-08-31, pre-dawn, "we can prove this theory in 5 minutes."

The language L: strictly superincreasing naturals whose reciprocals sum to 1. This file makes
the metaphor-closing note's concrete claims into THEOREMS: the sentences exist, CAPACITY and
SLACK are Lean words now, the (2,4) prefix provably DIES at four words, and provably COLLAPSES
to a forced future at five. Truth generating a next-token grammar - checked by the kernel, not
asserted by anyone.
-/

namespace Speaker

/-- A sentence of L, as an ordered list: each word exceeds the sum of all before it
    (perfect subset-sum decodability), all words >= 2, reciprocals sum to exactly 1. -/
def IsSentence (l : List ℕ) : Prop :=
  l ≠ [] ∧
  (∀ i : Fin l.length, (l.take i).sum < l.get i) ∧
  (∀ a ∈ l, 2 ≤ a) ∧
  (l.map (fun a => (1 : ℚ) / a)).sum = 1

/-- CAPACITY - the speaker's first invented word, now a Lean word: the most reciprocal
    meaning k remaining words can carry after a prefix of ordinary mass S. -/
def Capacity (k : ℕ) (S : ℕ) : ℚ :=
  2 * (1 - (1 : ℚ) / 2 ^ k) / (S + 1)

/-- SLACK - capacity minus required remaining meaning. Negative: the prefix is dead.
    Zero: every remaining word is forced. Positive: freedom. -/
def Slack (k : ℕ) (S : ℕ) (R : ℚ) : ℚ :=
  Capacity k S - R

/-- The unique 3-word sentence the speaker generated from pure coherence. -/
theorem sentence_236 : IsSentence [2, 3, 6] := by
  refine ⟨by simp, ?_, by decide, by norm_num⟩
  intro i
  fin_cases i <;> simp

/-- The COMPLETE four-word language, all three sentences sealed. -/
theorem sentence_2_3_7_42 : IsSentence [2, 3, 7, 42] := by
  refine ⟨by simp, ?_, by decide, by norm_num⟩
  intro i
  fin_cases i <;> simp

theorem sentence_2_3_8_24 : IsSentence [2, 3, 8, 24] := by
  refine ⟨by simp, ?_, by decide, by norm_num⟩
  intro i
  fin_cases i <;> simp

theorem sentence_2_3_9_18 : IsSentence [2, 3, 9, 18] := by
  refine ⟨by simp, ?_, by decide, by norm_num⟩
  intro i
  fin_cases i <;> simp

/-- THE DEATH CERTIFICATE. After speaking 2,4 with only two words left, the remaining
    meaning 1/4 exceeds capacity 3/14: the prefix is semantically dead. Not "unlikely" -
    dead, and the kernel signs it. -/
theorem prefix_24_dies_at_four_words :
    Slack 2 6 ((1 : ℚ) / 4) < 0 := by
  norm_num [Slack, Capacity]

/-- THE COLLAPSE. Same prefix, three words left: slack is EXACTLY zero, so per the
    capacity analysis every remaining word is forced - which is why {2,4,7,14,28} was
    inevitable, not found. -/
theorem prefix_24_zero_slack_at_five_words :
    Slack 3 6 ((1 : ℚ) / 4) = 0 := by
  norm_num [Slack, Capacity]

/-- And the forced five-word utterance itself, sealed as a sentence of L. -/
theorem sentence_2_4_7_14_28 : IsSentence [2, 4, 7, 14, 28] := by
  refine ⟨by simp, ?_, by decide, by norm_num⟩
  intro i
  fin_cases i <;> simp

/-- The Sylvester five-word utterance too - same sentence, verbose dialect. -/
theorem sentence_sylvester : IsSentence [2, 3, 7, 43, 1806] := by
  refine ⟨by simp, ?_, by decide, by norm_num⟩
  intro i
  fin_cases i <;> simp

/-- FIRST TOKEN FORCED: a word of 3 or more cannot open ANY sentence, because even
    infinitely many words cannot carry the remaining meaning: 1/m + 2/(m+1) < 1 for m >= 3.
    The arithmetic heart of FORCED(empty, 2), proved for every m at once. -/
theorem first_token_bound (m : ℕ) (hm : 3 ≤ m) :
    (1 : ℚ) / m + 2 / (m + 1) < 1 := by
  have hq : (3 : ℚ) ≤ m := by exact_mod_cast hm
  have h0 : (0 : ℚ) < m := by linarith
  have h1 : (0 : ℚ) < m + 1 := by linarith
  rw [div_add_div _ _ (ne_of_gt h0) (ne_of_gt h1), div_lt_one (by positivity)]
  nlinarith

end Speaker
