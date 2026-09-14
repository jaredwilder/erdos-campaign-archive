import Mathlib

/-!
SCALE-DUALITY, kernel-sealed. 2026-08-31 morning.

In flow run MATH-SPEAKER-FLOW-001 (40 utterances, replicated locally, receipt
oracle/evidence/speaker-flow-001/) the speaker discovered, unprompted, that a doubling phrase
T, 2T, 4T, ..., 2^(k-1) T has two readings - ordinary mass M = T(2^k - 1) and reciprocal mass
R = 2(2^k - 1)/(2^k T) - and that their PRODUCT forgets the scale entirely. The chain was
FORCED -> DOUBLING -> BINARY -> DUAL READING -> SCALE INVARIANT; the previous sentence made the
next available. Python checked it symbolically; this file makes it a theorem.
-/

namespace Speaker

/-- Ordinary mass of the doubling phrase T, 2T, ..., 2^(k-1)T. -/
def dblMass (T : ℚ) (k : ℕ) : ℚ := T * (2 ^ k - 1)

/-- Reciprocal mass of the same phrase. -/
def dblRmass (T : ℚ) (k : ℕ) : ℚ := 2 * (2 ^ k - 1) / (2 ^ k * T)

/-- ⭐ SCALE-DUALITY. The product of the two readings is independent of T: the ordinary
    reading scales with the phrase, the reciprocal reading scales against it, and what
    survives translation between the two semantics carries no trace of the scale. -/
theorem scale_duality (T : ℚ) (hT : T ≠ 0) (k : ℕ) :
    dblMass T k * dblRmass T k = 2 * (2 ^ k - 1) ^ 2 / 2 ^ k := by
  unfold dblMass dblRmass
  have h2 : (2 : ℚ) ^ k ≠ 0 := by positivity
  field_simp

/-- The invariance stated as invariance: any two nonzero scales give the same product. -/
theorem scale_duality_invariant (T U : ℚ) (hT : T ≠ 0) (hU : U ≠ 0) (k : ℕ) :
    dblMass T k * dblRmass T k = dblMass U k * dblRmass U k := by
  rw [scale_duality T hT k, scale_duality U hU k]

end Speaker
