import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def TriangleFree {α : Type*} (G : SimpleGraph α) : Prop :=
  ∀ a b c : α, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)

noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (G : SimpleGraph (Fin n)), TriangleFree G ∧ k = G.chromaticNumber}

theorem msl_erdos1104_a_m05_c2 : ∃ (c₁ : ℝ), 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ᶠ (n : ℕ) in Filter.atTop,
 (c₁ : ℝ) * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) ≤ ((f n : ℕ) : ℝ) := by sorry
