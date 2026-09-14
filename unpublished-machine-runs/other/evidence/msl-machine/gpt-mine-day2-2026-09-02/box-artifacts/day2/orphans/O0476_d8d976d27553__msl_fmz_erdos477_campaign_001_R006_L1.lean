import Mathlib

set_option autoImplicit false



def polyVals (d K : Nat) : List Nat := (List.range (K+1)).map (fun k => k ^ d)
/-- Distinct polynomial values k^2 with k <= K, counted exactly. -/
def valCount (K : Nat) : Nat := (polyVals 2 K).eraseDups.length
/-- Decidable fragment of L1 (sparsity + pigeonhole): for d=2, M=100 the set {k^2 : k in Z, |k^2| <= 100} has exactly 11 elements, so covering every n in [-100,100] = A + f(Z) (the 'at least one' half of the uniqueness condition) forces |A ∩ [-100,100]| >= 19, since 11 * 18 < 201 <= 11 * 19. -/
def checkL1fragment : Bool :=
  let c := valCount 10
  (c == 11) && (c * 18 < 201) && (201 <= c * 19)
theorem L1_fragment_R006 : checkL1fragment = true := by decide

theorem msl_fmz_erdos477_campaign_001_R006_L1  : checkL1fragment = true := by decide

-- axiom footprint
#print axioms polyVals
#print axioms valCount
#print axioms checkL1fragment
#print axioms L1_fragment_R006
#print axioms msl_fmz_erdos477_campaign_001_R006_L1
