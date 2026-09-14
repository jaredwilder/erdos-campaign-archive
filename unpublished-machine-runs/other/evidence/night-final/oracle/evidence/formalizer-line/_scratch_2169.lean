import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Pointwise
open scoped BigOperators

def countUpTo (S : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun n => n ∈ S)).card

def lowerDensity (S : Set ℕ) : ℝ :=
  sSup {x : ℝ |
    ∀ᶠ N : ℕ in Filter.atTop,
      x ≤ (countUpTo S N : ℝ) / ((N + 1 : ℕ) : ℝ)}

def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun a => a ∈ A ∧ n - a ∈ A)).card

def erdos749 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A : Set ℕ,
      lowerDensity (A + A) ≥ 1 - ε ∧
        ∃ C : ℕ, ∀ n : ℕ, representationCount A n ≤ C

def finitePairCount {N : ℕ} (A : Finset (Fin N)) (n : Fin N) : ℕ :=
  ((A.product A).filter
    (fun p : Fin N × Fin N => p.1.val + p.2.val = n.val)).card

def finiteSumCount {N : ℕ} (A : Finset (Fin N)) : ℕ :=
  (Finset.univ.filter
    (fun n : Fin N =>
      ∃ a : Fin N, a ∈ A ∧
        ∃ b : Fin N, b ∈ A ∧ a.val + b.val = n.val)).card

def finiteApprox (ε C N : ℕ) : Prop :=
  0 < ε ∧
    ∃ A : Finset (Fin N),
      finiteSumCount A ≥ N - ε ∧
        ∀ n : Fin N, finitePairCount A n ≤ C

theorem witness_pos : finiteApprox 1 2 1 := by
  unfold finiteApprox
  refine ⟨by norm_num, ∅, ?_, ?_⟩
  · simp [finiteSumCount]
  · intro n
    simp [finitePairCount]

theorem witness_neg : ¬ finiteApprox 1 0 2 := by
  intro h
  rcases h with ⟨_, A, hsum, hpair⟩
  have hcard : 0 < finiteSumCount A := by
    omega
  unfold finiteSumCount at hcard
  rcases Finset.card_pos.mp hcard with ⟨n, hn⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
  rcases hn with ⟨a, ha, b, hb, hab⟩
  have hpairpos : 0 < finitePairCount A n := by
    unfold finitePairCount
    apply Finset.card_pos.mpr
    refine ⟨(a, b), ?_⟩
    simp [ha, hb, hab]
  have hz := hpair n
  omega

theorem erdos749_open : erdos749 := by
  sorry

end