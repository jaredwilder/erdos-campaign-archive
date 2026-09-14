import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def TriangleFree {α : Type*} (G : SimpleGraph α) : Prop :=
  ∀ a b c : α, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)

noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (G : SimpleGraph (Fin n)), TriangleFree G ∧ k = G.chromaticNumber}

theorem msl_erdos1104_a_m05_c1 : ∀ (n : ℕ), ∃ (G : SimpleGraph (Fin n)), TriangleFree G ∧ (f n : ℕ) = G.chromaticNumber := by sorry
