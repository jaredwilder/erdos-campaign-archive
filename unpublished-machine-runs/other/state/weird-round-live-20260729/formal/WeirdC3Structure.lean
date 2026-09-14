import Mathlib

namespace WeirdC3Structure

def c3 (x₁ x₂ x₃ x₄ : ℤ) : Prop := x₁ - 3*x₂ + 3*x₃ - x₄ = 0

def PairwiseDistinct4 (x₁ x₂ x₃ x₄ : ℤ) : Prop :=
  x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₃ ≠ x₄

/-- The balanced-middle semantic species produces a genuine ordered C3 violation. -/
theorem balancedMiddle
    (a x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + z = 2*y) :
    PairwiseDistinct4 a (a+x) (a+x+y) (a+x+y+z) ∧
      c3 a (a+x) (a+x+y) (a+x+y+z) := by
  constructor
  · unfold PairwiseDistinct4
    omega
  · unfold c3
    omega

/-- The triple-end species `z = 3x` produces a violation after the required permutation. -/
theorem tripleEnd
    (a x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : z = 3*x) :
    PairwiseDistinct4 (a+x+y) a (a+x) (a+x+y+z) ∧
      c3 (a+x+y) a (a+x) (a+x+y+z) := by
  constructor
  · unfold PairwiseDistinct4
    omega
  · unfold c3
    omega

/-- The affine-tail species `z = 3x+2y` produces a violation after permutation. -/
theorem affineTail
    (a x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : z = 3*x + 2*y) :
    PairwiseDistinct4 (a+x) a (a+x+y) (a+x+y+z) ∧
      c3 (a+x) a (a+x+y) (a+x+y+z) := by
  constructor
  · unfold PairwiseDistinct4
    omega
  · unfold c3
    omega

def avoidsC3 (s : List ℕ) : Bool :=
  s.all fun x₁ => s.all fun x₂ => s.all fun x₃ => s.all fun x₄ =>
    if x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₃ ≠ x₄
    then (x₁ : ℤ) - 3*x₂ + 3*x₃ - x₄ ≠ 0 else true

def birth : List ℕ := [1,4,6,8,11,24,28,41,44,46,48,51]

theorem birthNodup : birth.Nodup := by native_decide
theorem birthCardinality : birth.length = 12 := by native_decide

/-- Exact target retained without asserting it before its finite upper certificate is kernel-translated. -/
def SpanTarget : Prop :=
  ∀ (s : Finset ℤ) (lo hi : ℤ), s.card = 12 →
    (∀ x₁ ∈ s, ∀ x₂ ∈ s, ∀ x₃ ∈ s, ∀ x₄ ∈ s,
      PairwiseDistinct4 x₁ x₂ x₃ x₄ → ¬ c3 x₁ x₂ x₃ x₄) →
    (∀ x ∈ s, lo ≤ x ∧ x ≤ hi) → hi - lo ≥ 50

#print axioms balancedMiddle
#print axioms tripleEnd
#print axioms affineTail

end WeirdC3Structure
