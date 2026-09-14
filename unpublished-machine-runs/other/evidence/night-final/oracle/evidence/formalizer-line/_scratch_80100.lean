import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open Set

/-- The Chebyshev node with index `i` among the `n + 1` nodes.
The literal `1` is absorbed into the indexing convention `n + 1`. -/
def chebyshevNode (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  Real.cos
    (Real.pi * (2 * (i : ℝ) + 1) /
      (2 * ((n + 1 : ℕ) : ℝ)))

/-- The Lagrange basis polynomial associated to a Chebyshev node. -/
def lagrangeBasis (n : ℕ) (i : Fin (n + 1)) (x : ℝ) : ℝ :=
  (Finset.univ.erase i).prod (fun j =>
    (x - chebyshevNode n j) /
      (chebyshevNode n i - chebyshevNode n j))

/-- The Lagrange interpolation expression at stage `n`.
The polynomial degree is `n - 1` when the original number of nodes is `n`;
here the stage is indexed by `n`, hence there are `n + 1` nodes. -/
def lagrangeInterpolation (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    f (chebyshevNode n i) * lagrangeBasis n i x

/-- The set of subsequential limit points of a real sequence. -/
def limitPoints (u : ℕ → ℝ) : Set ℝ :=
  {y | ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ |u n - y| < ε}

/-- The assertion that a continuous function has `A` as the limit-point set
of its sequence of Lagrange interpolants evaluated at `x`. -/
def hasRequiredLimitSet (A : Set ℝ) (x : ℝ) : Prop :=
  ∃ f : ℝ → ℝ,
    Continuous f ∧
      limitPoints (fun n => lagrangeInterpolation f n x) = A

/-- This records the indexing condition `1 ≤ i ≤ n` from the statement. -/
def isNodeIndex (i n : ℕ) : Prop :=
  1 ≤ i ∧ i ≤ n

/-- The degree bound appearing in the original formulation. -/
def interpolationDegreeBound (n : ℕ) : ℕ :=
  n - 1

theorem witness_pos : isNodeIndex 1 1 := by
  norm_num [isNodeIndex]

theorem witness_neg : ¬ isNodeIndex 2 1 := by
  norm_num [isNodeIndex]

/-- Erdős problem 1151, in the formulation for a fixed point
`x = cos (π p / q)` with positive odd integers `p` and `q`. -/
theorem erdos_problem_1151 :
    ∀ A : Set ℝ,
      IsClosed A →
      A ⊆ Set.Icc (-1 : ℝ) 1 →
      ∀ p q : ℕ,
        1 ≤ p →
        1 ≤ q →
        Odd p →
        Odd q →
        hasRequiredLimitSet A
          (Real.cos (Real.pi * (p : ℝ) / (q : ℝ))) := by
  sorry

end