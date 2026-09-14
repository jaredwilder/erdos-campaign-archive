import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  A sequence of nonnegative integers is used for the integer sequence in the
  question.  The source numerals 1, 2, and 3 occur below in the corresponding
  indexed and arithmetic conditions.
-/

def IsSquarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ n

def PrimeShift (a : ℕ → ℕ) (n k : ℕ) : Prop :=
  Nat.Prime (n + a k)

def SquarefreeShift (a : ℕ → ℕ) (n k : ℕ) : Prop :=
  IsSquarefree (n + a k)

def AlwaysPrime (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k : ℕ, PrimeShift a n k

def AlwaysSquarefree (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k : ℕ, SquarefreeShift a n k

def InfinitelyManyPrimeShifts (a : ℕ → ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < n ∧ AlwaysPrime a n

def InfinitelyManySquarefreeShifts (a : ℕ → ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < n ∧ AlwaysSquarefree a n

def AdmissibleSequence (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ Filter.Tendsto a Filter.atTop Filter.atTop

def PrimeQuestion : Prop :=
  ∀ a : ℕ → ℕ, AdmissibleSequence a →
    (∃ n : ℕ, AlwaysPrime a n) →
      InfinitelyManyPrimeShifts a

def SquarefreeQuestion : Prop :=
  ∀ a : ℕ → ℕ, AdmissibleSequence a →
    (∃ n : ℕ, AlwaysSquarefree a n) →
      InfinitelyManySquarefreeShifts a

def PowerSequence (k : ℕ) : ℕ :=
  2 ^ (2 ^ k)

def PowerAlwaysPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, Nat.Prime (n + PowerSequence k)

def PowerAlwaysSquarefree (n : ℕ) : Prop :=
  ∀ k : ℕ, IsSquarefree (n + PowerSequence k)

def PowerInfinitelyOftenPrime : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ k : ℕ, Nat.Prime (n + PowerSequence k)

def PowerInfinitelyOftenSquarefree : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < n ∧ ∃ k : ℕ, IsSquarefree (n + PowerSequence k)

/-
  A bounded, decidable finite approximation used for concrete kernel-checkable
  witnesses.
-/
def HasPrimeShift (A : Finset ℕ) (N : ℕ) : Prop :=
  ∃ n ∈ Finset.range N, ∀ k ∈ A, Nat.Prime (n + k)

def HasSquarefreeShift (A : Finset ℕ) (N : ℕ) : Prop :=
  ∃ n ∈ Finset.range N, ∀ k ∈ A, IsSquarefree (n + k)

theorem witness_pos : HasPrimeShift (∅ : Finset ℕ) 1 := by
  refine ⟨0, by simp, ?_⟩
  simp

theorem witness_neg : ¬ HasPrimeShift ({1} : Finset ℕ) 1 := by
  rintro ⟨n, hn, hprime⟩
  have hnlt : n < 1 := by
    simpa using hn
  have hn0 : n = 0 := by
    omega
  subst n
  have hp : Nat.Prime (0 + 1) := hprime 1 (by simp)
  norm_num at hp

/-
  The resolution records the counterexamples to the two universal questions
  and the nonexistence of an n for which n + 2^(2^k) is always prime.
-/
theorem erdos_1209 :
    ¬ PrimeQuestion ∧
    ¬ SquarefreeQuestion ∧
    ¬ (∃ n : ℕ, PowerAlwaysPrime n) := by
  sorry

end