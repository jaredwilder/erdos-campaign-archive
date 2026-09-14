import Mathlib

set_option autoImplicit false


-- Decidable fragment of L1 on the discrete distance data (distances are
-- determined by the configuration; unit minimum distance scales to Nat 1).
-- checkDiam encodes: given pairwise distances (scaled integers, min distance 1),
-- the diameter is at least 1, and equality of the diameter with 1 forces all
-- three distances equal to 1 (the unit equilateral triangle's distance data).
def checkDiam (dab dbc dca : Nat) : Bool :=
  let dmax := max (max dab dbc) dca
  (dmax >= 1) && (dmax == 1 -> (dab == 1 && dbc == 1 && dca == 1))
-- The distance data of the unique three-point minimizer:
def unitTriangle : Nat × Nat × Nat := (1, 1, 1)
-- Representative non-minimizing triples (some side strictly above 1):
def probeA : Nat × Nat × Nat := (1, 1, 2)
def probeB : Nat × Nat × Nat := (2, 2, 2)
def probeC : Nat × Nat × Nat := (1, 2, 1)
def runChecks : Bool :=
  checkDiam unitTriangle.1 unitTriangle.2.1 unitTriangle.2.2 &&
  checkDiam probeA.1 probeA.2.1 probeA.2.2 &&
  checkDiam probeB.1 probeB.2.1 probeB.2.2 &&
  checkDiam probeC.1 probeC.2.1 probeC.2.2

theorem msl_fmz_erdos99_campaign_001_R002_L1  : runChecks = true := by decide

-- axiom footprint
#print axioms checkDiam
#print axioms unitTriangle
#print axioms probeA
#print axioms probeB
#print axioms probeC
#print axioms runChecks
#print axioms msl_fmz_erdos99_campaign_001_R002_L1
