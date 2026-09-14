import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def OnInterval (x : ℝ) : Prop :=
  -1 ≤ x ∧ x ≤ 1

def ErdosStatement (C ε : ℝ) (n : ℕ) : Prop :=
  ∀ x : Fin n → ℝ,
    (∀ i, OnInterval (x i)) →
      ∃ y : Fin n → ℝ,
        (∀ i, OnInterval (y i)) ∧
          ∀ m : ℕ, (m : ℝ) < (1 + ε) * (n : ℝ) →
            ∀ P : Polynomial ℝ, P.natDegree = m →
              ((Finset.univ.filter
                    (fun i : Fin n => P.eval (x i) = y i)).card : ℝ) ≥
                (1 - ε) * (n : ℝ) →
                ∃ z : ℝ, OnInterval z ∧ C < |P.eval z|

def Erdos1133 (C : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ErdosStatement C ε n

theorem erdos_1133 (C : ℝ) (hC : 0 < C) : Erdos1133 C := by
  sorry

def discretePoint (a : Fin 3) : ℤ :=
  (a : ℤ) - 1

def discreteEval {m : ℕ} (p : Fin (m + 1) → Fin 3) (z : Fin 3) : ℤ :=
  ∑ i, discretePoint (p i) * (discretePoint z) ^ (i : ℕ)

def DiscreteStatement (C ε n : ℕ) : Prop :=
  ∀ x : Fin n → Fin 3,
    ∃ y : Fin n → Fin 3,
      ∀ m : ℕ, m < (1 + ε) * n →
        ∀ p : Fin (m + 1) → Fin 3,
          ((Finset.univ.filter
                (fun i : Fin n =>
                  discreteEval p (x i) = discretePoint (y i))).card) ≥
              (1 - ε) * n →
            ∃ z : Fin 3,
              (C : ℤ) < |discreteEval p z|

theorem witness_pos : DiscreteStatement 0 1 0 := by
  intro x
  refine ⟨fun _ => 0, ?_⟩
  intro m hm
  omega

theorem witness_neg : ¬ DiscreteStatement 0 1 1 := by
  intro h
  let x : Fin 1 → Fin 3 := fun _ => 0
  obtain ⟨y, hy⟩ := h x
  let p : Fin (0 + 1) → Fin 3 := fun _ => 1
  have hm : 0 < (1 + 1) * 1 := by
    norm_num
  have hcard :
      ((Finset.univ.filter
          (fun i : Fin 1 =>
            discreteEval p (x i) = discretePoint (y i))).card) ≥
        (1 - 1) * 1 := by
    simp
  obtain ⟨z, hz⟩ := hy 0 hm p hcard
  have heval : discreteEval p z = 0 := by
    norm_num [p, discreteEval, discretePoint]
  rw [heval] at hz
  norm_num at hz

end