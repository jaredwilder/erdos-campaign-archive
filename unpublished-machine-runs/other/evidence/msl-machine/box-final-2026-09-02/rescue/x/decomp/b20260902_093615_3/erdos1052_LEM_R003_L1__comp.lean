import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

/-- `d` is a unitary divisor of `n`: `d ∣ n` and `d` is coprime to `n / d`. -/
def IsUnitaryDivisor (d : ℕ) (n : ℕ) : Prop := d ∣ n ∧ Nat.gcd d (n / d) = (1 : ℕ)

/-- The Finset of unitary divisors of `n`, reconstructed by filtering `Nat.divisors n`;
membership in `Nat.divisors n` already supplies `d ∣ n`. -/
def unitaryDivisorFinset (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).filter (fun (d : ℕ) => Nat.gcd d (n / d) = (1 : ℕ))

/-- `σ*(n)`: the sum of all unitary divisors of `n`, including `n` itself. -/
def sigmaStar (n : ℕ) : ℕ := (unitaryDivisorFinset n).sum id

/-- `n` is unitary perfect iff it is the sum of its unitary divisors other than itself,
i.e. `σ*(n) = 2 * n` (this is the vocabulary of the frozen contract root). -/
def IsUnitaryPerfect (n : ℕ) : Prop := sigmaStar n = (2 : ℕ) * n

/-- The four hits of the exhaustive exact-integer sweep over `1 ≤ n ≤ 10^7`. -/
def unitaryPerfectSweepHits : Finset ℕ :=
  {(6 : ℕ), (60 : ℕ), (90 : ℕ), (87360 : ℕ)}

theorem msl_erdos1052_lem_r003_l1_composition : ((∀ (n : ℕ), n ∈ Finset.Icc (1 : ℕ) (10000000 : ℕ) → IsUnitaryPerfect n → n ∈ unitaryPerfectSweepHits) ∧ (sigmaStar (87360 : ℕ) = (2 : ℕ) * (87360 : ℕ)) ∧ (∀ (n : ℕ), n ∈ Finset.Icc (1 : ℕ) (10000000 : ℕ) → Odd n → ¬ IsUnitaryPerfect n)) → ((∀ (n : ℕ), n ∈ Finset.Icc (1 : ℕ) (10000000 : ℕ) → IsUnitaryPerfect n → n ∈ unitaryPerfectSweepHits) ∧ (∀ (n : ℕ), n ∈ unitaryPerfectSweepHits → sigmaStar n = (2 : ℕ) * n) ∧ (∀ (n : ℕ), n ∈ Finset.Icc (1 : ℕ) (10000000 : ℕ) → Odd n → ¬ IsUnitaryPerfect n)) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos1052_lem_r003_l1_composition
