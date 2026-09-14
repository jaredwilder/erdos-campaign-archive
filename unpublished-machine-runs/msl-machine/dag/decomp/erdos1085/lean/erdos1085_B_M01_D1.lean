import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Classical

/-- `unitPairs d s` is the number of unordered pairs of points of `s` at Euclidean distance exactly `1`; the filtered Cartesian square counts each unordered pair twice, hence the division by two. -/
noncomputable def unitPairs (d : Nat) (s : Finset (EuclideanSpace ℝ (Fin d))) : Nat :=
  ((s ×ˢ s).filter (fun p => dist p.1 p.2 = (1 : ℝ))).card / (2 : Nat)

/-- `upperEstimate d n`: every `n`-point set of `ℝ^d` has at most this many unit pairs. Dimension 1: `n - 1`; dimension 2: Spencer–Szemerédi–Trotter `64 * n^(4/3)`; dimension 3: `K_{3,3}`-free plus Kővári–Sós–Turán, `8 * n^(5/3)`; dimensions `≥ 4` (and `d = 0`): the trivial `n * (n - 1) / 2`. -/
noncomputable def upperEstimate (d n : Nat) : ℝ :=
  match d with
  | 1 => (n : ℝ) - (1 : ℝ)
  | 2 => (64 : ℝ) * ((n : ℝ) ^ ((4 : ℝ) / (3 : ℝ)))
  | 3 => (8 : ℝ) * ((n : ℝ) ^ ((5 : ℝ) / (3 : ℝ)))
  | _ => ((n : ℝ) * ((n : ℝ) - (1 : ℝ))) / (2 : ℝ)

/-- `lowerEstimate d n`: some `n`-point set of `ℝ^d` has at least this many unit pairs. Dimension 1: `n - 1` (arithmetic progression); dimension 2: Erdős's lattice construction; dimension 3: lattice construction via sums of three squares; dimensions `≥ 4`: Lenz's orthogonal circles. -/
noncomputable def lowerEstimate (d n : Nat) : ℝ :=
  match d with
  | 1 => (n : ℝ) - (1 : ℝ)
  | 2 => ((n : ℝ) / (4 : ℝ)) *
      ((n : ℝ) ^ ((1 : ℝ) / ((3 : ℝ) * (Real.log (Real.log ((n : ℝ) + (2 : ℝ))) + (2 : ℝ)))))
  | 3 => ((n : ℝ) ^ ((4 : ℝ) / (3 : ℝ))) / (1000 : ℝ)
  | _ => ((n : ℝ) * (n : ℝ)) / (8 : ℝ)

theorem msl_erdos1085_b_m01_c1 (n : Nat) (hn : 2 ≤ n) : (∀ s : Finset (EuclideanSpace ℝ (Fin 1)), s.card = n → (unitPairs 1 s : ℝ) ≤ (n : ℝ) - (1 : ℝ)) ∧ (∃ s : Finset (EuclideanSpace ℝ (Fin 1)), s.card = n ∧ (n : ℝ) - (1 : ℝ) ≤ (unitPairs 1 s : ℝ)) := by sorry
