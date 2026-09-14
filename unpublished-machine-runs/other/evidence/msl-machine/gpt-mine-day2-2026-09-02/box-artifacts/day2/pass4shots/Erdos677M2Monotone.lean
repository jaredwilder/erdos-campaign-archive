import Mathlib

set_option autoImplicit false

def erdos677M2 (n : ℕ) : ℕ := (n + 1) * (n + 2)

/-- Polynomial monotonicity core for the k=2 specialization. -/
theorem erdos677_M2_strictMono : StrictMono erdos677M2 := by
  intro a b hab
  dsimp [erdos677M2]
  nlinarith

-- axiom footprint
#print axioms erdos677_M2_strictMono
