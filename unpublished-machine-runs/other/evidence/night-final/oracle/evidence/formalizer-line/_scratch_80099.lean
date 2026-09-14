import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  Some numerical metadata occurring in the source entry.
-/
def originalProblemNumber : Nat := 1212
def sourceResolutionPage : Nat := 114
def sourcePaperYearSuffix : Nat := 71
def sourceBounty : Nat := 25
def sourceBlockSize : Nat := 50
def sourceThresholdIndex : Nat := 4

abbrev Vertex := ℕ × ℕ

def Visible (v : Vertex) : Prop :=
  Nat.Coprime v.1 v.2

def Composite (n : ℕ) : Prop :=
  1 < n ∧ ¬ Nat.Prime n

def GoodVertex (v : Vertex) : Prop :=
  Visible v ∧
    1 < min v.1 v.2 ∧
    (Composite v.1 ∨ Composite v.2)

def Adjacent (u v : Vertex) : Prop :=
  (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) ∨
    (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1))

def IsFiniteGoodPath (n : ℕ) (p : Fin n → Vertex) : Prop :=
  (∀ i : Fin n, GoodVertex (p i)) ∧
    (∀ i j : Fin n, i.val + 1 = j.val → Adjacent (p i) (p j))

def InfiniteGoodPath : Prop :=
  ∃ p : ℕ → Vertex,
    (∀ n : ℕ, GoodVertex (p n)) ∧
      (∀ n : ℕ, Adjacent (p n) (p (n + 1))) ∧
        (∀ B : ℕ, ∃ n : ℕ, B < (p n).1 + (p n).2)

theorem witness_pos :
    IsFiniteGoodPath 2
      (fun i : Fin 2 => if i.val = 0 then (9, 4) else (9, 5)) := by
  unfold IsFiniteGoodPath
  constructor
  · intro i
    fin_cases i <;>
      norm_num [GoodVertex, Visible, Composite, Nat.Coprime]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Adjacent]

theorem witness_neg :
  ¬ IsFiniteGoodPath 1 (fun _ : Fin 1 => (2, 3)) := by
  unfold IsFiniteGoodPath
  intro h
  rcases h with ⟨hgood, _⟩
  have hv := hgood (⟨0, by norm_num⟩ : Fin 1)
  norm_num [GoodVertex, Visible, Composite, Nat.Coprime] at hv

theorem erdos_1212 : InfiniteGoodPath := by
  sorry

end