import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- An `r`-uniform hypergraph on `n` vertices. -/
def Hypergraph (r n : ℕ) :=
  {E : Finset (Finset (Fin n)) // ∀ e ∈ E, e.card = r}

/-- The family of all `r`-uniform hypergraphs on `d` vertices with `e` edges. -/
def HypergraphFamily (r e d : ℕ) : Finset (Hypergraph r d) := by
  classical
  letI : Fintype (Hypergraph r d) := by
    unfold Hypergraph
    infer_instance
  exact
    (Finset.univ : Finset (Hypergraph r d)).filter (fun H => H.1.card = e)

/-- A hypergraph embedding, preserving every edge. -/
def Embeds {r d n : ℕ} (F : Hypergraph r d) (G : Hypergraph r n) : Prop :=
  ∃ f : Fin d → Fin n,
    Function.Injective f ∧
      ∀ E ∈ F.1, E.image f ∈ G.1

/-- The `r`-uniform hypergraphs on `n` vertices avoiding the prescribed family. -/
def Admissible (r e d n : ℕ) : Finset (Hypergraph r n) := by
  classical
  letI : Fintype (Hypergraph r n) := by
    unfold Hypergraph
    infer_instance
  exact
    (Finset.univ : Finset (Hypergraph r n)).filter
      (fun G => ∀ F ∈ HypergraphFamily r e d, ¬ Embeds F G)

/-- The extremal number for the family of all `e`-edge hypergraphs on `d` vertices. -/
def Extremal (r e d n : ℕ) : ℕ :=
  (Admissible r e d n).sup (fun G => G.1.card)

/--
A natural-number formulation of `Extremal r e d n = o(n^2)`: for every
positive reciprocal scale, the corresponding quadratic bound eventually holds.
-/
def Subquadratic (r e d : ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    k * Extremal r e d n ≤ n ^ 2

/-- The minimal number of vertices in the definition of `d_r(e)`. -/
def d_r (r e : ℕ) : ℕ :=
  sInf {d : ℕ | Subquadratic r e d}

/-- The numerical assertion made by the conjecture at a specified value of `d`. -/
def TargetValue (r e d : ℕ) : Prop :=
  r ≥ 3 ∧ e ≥ 3 ∧ d = (r - 2) * e + 3

theorem witness_pos : TargetValue 3 3 6 := by
  norm_num [TargetValue]

theorem witness_neg : ¬ TargetValue 3 3 5 := by
  norm_num [TargetValue]

theorem erdos_problem_1178 (r e : ℕ) (hr : r ≥ 3) (he : e ≥ 3) :
    d_r r e = (r - 2) * e + 3 := by
  sorry

end