import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def PrimeIndex (n : ℕ) := {p : Fin (n + 1) // Nat.Prime p.1}

def BoundedGood (n H M : ℕ) : Prop :=
  ∀ m ∈ Finset.Icc 1 M,
    ∃ a : PrimeIndex n → Fin (m + H + 1),
      (∀ p : PrimeIndex n,
        m < (a p : ℕ) ∧ (a p : ℕ) < m + H ∧ p.1.1 ∣ (a p : ℕ)) ∧
      (∀ ⦃p q : PrimeIndex n⦄, p ≠ q → a p ≠ a q)

def Good (n H : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∃ a : PrimeIndex n → ℕ,
      (∀ p : PrimeIndex n,
        m < a p ∧ a p < m + H ∧ p.1.1 ∣ a p) ∧
      (∀ ⦃p q : PrimeIndex n⦄, p ≠ q → a p ≠ a q)

noncomputable def h (n : ℕ) : ℕ :=
  sInf {H : ℕ | Good n H}

theorem witness_pos : BoundedGood 2 2 1 := by
  intro m hm
  have hm' : 1 ≤ m ∧ m ≤ 1 := Finset.mem_Icc.mp hm
  have hm_eq : m = 1 := by omega
  subst m
  have hpval : ∀ p : PrimeIndex 2, (p.1 : ℕ) = 2 := by
    intro p
    have hlow : 2 ≤ (p.1 : ℕ) := p.property.two_le
    have hupp := p.1.isLt
    omega
  have hpeq : ∀ p q : PrimeIndex 2, p = q := by
    intro p q
    apply Subtype.ext
    apply Fin.ext
    exact (hpval p).trans (hpval q).symm
  let a : PrimeIndex 2 → Fin (1 + 2 + 1) :=
    fun _ => ⟨2, by decide⟩
  refine ⟨a, ?_, ?_⟩
  · intro p
    norm_num [a, hpval p]
  · intro p q hpq
    exact (hpq (hpeq p q)).elim

theorem witness_neg : ¬ BoundedGood 2 1 1 := by
  intro h
  rcases h 1 (by simp) with ⟨a, ha, _⟩
  let p : PrimeIndex 2 := ⟨⟨2, by decide⟩, by decide⟩
  have hp := (ha p).1
  have hp' := (ha p).2.1
  omega

theorem erdos_pomerance_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (h n : ℝ) ≤
        C * Real.rpow (n : ℝ) ((3 : ℝ) / 2) /
          Real.sqrt (Real.log (n : ℝ)) := by
  sorry

end