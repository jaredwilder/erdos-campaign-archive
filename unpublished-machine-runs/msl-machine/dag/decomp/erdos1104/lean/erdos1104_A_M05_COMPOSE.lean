import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def TriangleFree {α : Type*} (G : SimpleGraph α) : Prop :=
  ∀ a b c : α, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)

noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (G : SimpleGraph (Fin n)), TriangleFree G ∧ k = G.chromaticNumber}

theorem msl_erdos1104_a_m05_composition : ((∀ (n : ℕ), ∃ (G : SimpleGraph (Fin n)), TriangleFree G ∧ (f n : ℕ) = G.chromaticNumber) ∧ (∃ (c₁ : ℝ), 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
 (c₁ : ℝ) * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) ≤ ((f n : ℕ) : ℝ)) ∧ (∃ (c₂ : ℝ), 2 ≤ c₂ ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
 ((f n : ℕ) : ℝ) ≤ c₂ * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)))) → (∃ (c₁ c₂ : ℝ), 0 < c₁ ∧ c₁ ≤ 1 ∧ 2 ≤ c₂ ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
 ((c₁ : ℝ) * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) ≤ ((f n : ℕ) : ℝ) ∧
  ((f n : ℕ) : ℝ) ≤ c₂ * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)))) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos1104_a_m05_composition
