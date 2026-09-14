import Mathlib

set_option autoImplicit false


def onCircle (c : ℚ × ℚ × ℚ) (p : ℚ × ℚ) : Bool :=
  (p.1 - c.1)^2 + (p.2 - c.2.1)^2 == c.2.2^2

def evades (p : ℚ × ℚ) (circles : List (ℚ × ℚ × ℚ)) : Bool :=
  circles.all (fun c => !(onCircle c p))

def inUnitDisc (p : ℚ × ℚ) : Bool := p.1^2 + p.2^2 ≤ 1

def sampleCircles : List (ℚ × ℚ × ℚ) :=
  [(0, 0, 1), (1, 0, 1), (0, 1, 1), (1/2, 0, 1/2), (0, 1/2, 3/4), (-1/3, 1/4, 2/3)]

def checkL1Fragment : Bool :=
  inUnitDisc (1/2, 0) && evades (1/2, 0) sampleCircles

theorem msl_fmz_erdos509_campaign_001_R004_L1_a2r4  : checkL1Fragment = true := by decide

-- axiom footprint
#print axioms onCircle
#print axioms evades
#print axioms inUnitDisc
#print axioms sampleCircles
#print axioms checkL1Fragment
#print axioms msl_fmz_erdos509_campaign_001_R004_L1_a2r4
