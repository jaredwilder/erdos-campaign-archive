import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

noncomputable def Tri2Area (p q r : ℂ) : ℝ :=
  |Complex.im (Complex.conj (q - p) * (r - p))| / (2 : ℝ)

/-- `Tri2Admissible n a`: every `n`-point set in the closed unit disk contains three
distinct points spanning a triangle of area at most `a`. -/
def Tri2Admissible (n : Nat) (a : ℝ) : Prop :=
  ∀ (S : Finset ℂ), (∀ (z : ℂ), z ∈ S → ‖z‖ ≤ (1 : ℝ)) → S.card = n →
    ∃ (p : ℂ), p ∈ S ∧ ∃ (q : ℂ), q ∈ S ∧ ∃ (r : ℂ), r ∈ S ∧
      p ≠ q ∧ q ≠ r ∧ p ≠ r ∧ Tri2Area p q r ≤ a

/-- The directly determined Erdős #507 quantity: the infimum of the triangle-area
bounds admissible for every `n`-point set in the closed unit disk. -/
noncomputable def erdos507Alpha (n : Nat) : ℝ :=
  sInf {a : ℝ | Tri2Admissible n a}

theorem msl_erdos507_a_m02_c2 (n : Nat) (hn : (3 : Nat) ≤ n) : Tri2Admissible n (erdos507Alpha n) := by sorry
