import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
universe u

structure ErdosGraph (V : Type u) where
  Adj : V → V → Prop
  symm : ∀ ⦃x y : V⦄, Adj x y → Adj y x
  loopless : ∀ x : V, ¬ Adj x x

def Colorable (G : ErdosGraph V) (C : Type u) : Prop :=
  ∃ f : V → C, ∀ ⦃x y : V⦄, G.Adj x y → f x ≠ f y

def ChromaticAleph1 (G : ErdosGraph V) : Prop :=
  (∃ C : Type u,
    Cardinal.mk C = Cardinal.aleph 1 ∧ Colorable G C) ∧
    ∀ C : Type u,
      Cardinal.mk C < Cardinal.aleph 1 →
        ¬ Colorable G C

structure ErdosSubgraph (G : ErdosGraph V) where
  carrier : Finset V
  Adj : carrier → carrier → Prop
  symm : ∀ ⦃x y : carrier⦄, Adj x y → Adj y x
  loopless : ∀ x : carrier, ¬ Adj x x
  edge_of : ∀ ⦃x y : carrier⦄, Adj x y → G.Adj x.1 y.1

def SubgraphColorable (H : ErdosSubgraph G) (C : Type u) : Prop :=
  ∃ f : H.carrier → C,
    ∀ ⦃x y : H.carrier⦄, H.Adj x y → f x ≠ f y

def HasChromaticNumber (H : ErdosSubgraph G) (n : ℕ) : Prop :=
  SubgraphColorable H (Fin n) ∧
    (n = 0 ∨ ¬ SubgraphColorable H (Fin (n - 1)))

theorem erdos_problem_110 :
    ∃ F : ℕ → ℕ, ∃ N : ℕ,
      ∀ {V : Type u} (G : ErdosGraph V),
        ChromaticAleph1 G →
          ∀ n : ℕ, N ≤ n →
            ∃ H : ErdosSubgraph G,
              H.carrier.card ≤ F n ∧ HasChromaticNumber H n := by
  sorry

end
