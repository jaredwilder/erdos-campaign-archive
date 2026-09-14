import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
structure BGraph (α : Type*) where
  adj : α → α → Bool
  symm : ∀ ⦃u v : α⦄, adj u v = adj v u
  loopless : ∀ u : α, adj u u = false

def BGraph.Degree {α : Type*} [Fintype α] [DecidableEq α]
    (G : BGraph α) (v : α) : ℕ :=
  (Finset.univ.filter (fun w => G.adj v w = true)).card

def BGraph.HasMinimumDegree {α : Type*} [Fintype α] [DecidableEq α]
    (G : BGraph α) (r : ℕ) : Prop :=
  ∀ v : α, r ≤ G.Degree v

def BGraph.IsBipartite {α : Type*} (G : BGraph α) : Prop :=
  ∃ color : α → Bool,
    ∀ ⦃u v : α⦄, G.adj u v = true → color u ≠ color v

def BGraph.IsSubgraphOf {α β : Type*} (H : BGraph α) (G : BGraph β) : Prop :=
  ∃ f : α → β,
    Function.Injective f ∧
      ∀ ⦃u v : α⦄, H.adj u v = true → G.adj (f u) (f v) = true

def BGraph.HFree {α β : Type*} (H : BGraph α) (G : BGraph β) : Prop :=
  ¬ H.IsSubgraphOf G

def BGraph.EdgeCount {α : Type*} [Fintype α] [DecidableEq α]
    (G : BGraph α) : ℝ :=
  ((Finset.univ.product Finset.univ).filter
      (fun p => G.adj p.1 p.2 = true)).card / 2

def extremalNumber {α : Type*} [Fintype α] [DecidableEq α]
    (H : BGraph α) (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ G : BGraph (Fin n), H.HFree G ∧ x = G.EdgeCount}

theorem erdos_problem_147
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : BGraph α) (r : ℕ) (hr : 2 ≤ r)
    (hmin : H.HasMinimumDegree r) (hbip : H.IsBipartite) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ c : ℝ, 0 < c ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          c * Real.rpow (n : ℝ)
              (2 - 1 / ((r : ℝ) - 1) + ε) ≤ extremalNumber H n := by
  sorry

end
