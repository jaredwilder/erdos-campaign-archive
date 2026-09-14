import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

-- Null-payload round bookkeeping for erdos1113:LEM:R009:L2 (CANDIDATE = "none").
def nullCandidate : String := ("none" : String)

-- The null candidate supplies no claims at all: it admits no falsifiable content.
def nullPayloadClaims : List Prop := ([] : List Prop)

-- The round's twelve attacks, indexed by the bounded set {1, ..., 12}.
def attackIndices : Finset Nat := Finset.Icc (1 : Nat) (12 : Nat)

-- The previously refuted child R008/L1, and this round's (empty) resupply list.
def r008L1 : String := ("erdos1113:R008:L1" : String)
def roundSupply : List String := ([] : List String)

-- Label under which a machine-checkable branch-A core would have to be supplied.
def branchACoreLabel : String := ("erdos1113:LEM:R009:L2:branchA" : String)

-- Attack i yields a counterexample iff it refutes some claim of the candidate.
def AttackCounterex (i : Nat) : Prop :=
  ∃ (c : Prop), c ∈ nullPayloadClaims ∧ i ∈ attackIndices ∧ ¬ c
def AttackVacuous (i : Nat) : Prop := ¬ AttackCounterex i

-- Covering vocabulary for the branch-A (∀P ∃n) determination.
def CoversAll (m : Nat) (P : Finset Nat) : Prop :=
  ∀ (k : Nat), ∃ (p : Nat), p ∈ P ∧ p ∣ ((2 : Nat) ^ k * m + 1)
def HasFinitePrimeCoveringSet (m : Nat) : Prop :=
  ∃ (P : Finset Nat), (∀ (p : Nat), p ∈ P → Nat.Prime p) ∧ CoversAll m P
-- Branch-A core: for every finite set of primes P there is an exponent k with
-- 2^k * m + 1 divisible by no member of P; this is what must be determined.
def BranchACore (m : Nat) : Prop :=
  ∀ (P : Finset Nat), (∀ (p : Nat), p ∈ P → Nat.Prime p) →
    ∃ (k : Nat), ∀ (p : Nat), p ∈ P → ¬ (p ∣ ((2 : Nat) ^ k * m + 1))

theorem msl_erdos1113_lem_r009_l2_c3 : attackIndices.card = (12 : Nat) ∧ ∀ (i : Nat), i ∈ attackIndices → AttackVacuous i := by sorry
