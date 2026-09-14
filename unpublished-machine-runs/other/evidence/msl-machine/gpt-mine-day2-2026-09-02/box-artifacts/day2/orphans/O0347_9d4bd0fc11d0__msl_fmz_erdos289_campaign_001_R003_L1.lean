import Mathlib

set_option autoImplicit false


def sumScaled (L : Nat) (a b : Nat) : Nat :=
  (List.range (b - a + 1)).foldl (fun s i => s + L / (a + i)) 0

def lcmRange (a b : Nat) : Nat :=
  (List.range (b - a + 1)).foldl (fun l i => Nat.lcm l (a + i)) 1

/-- k=1 fragment: no interval [a,b] with 2 <= a, length >= 2, b < B has sum of reciprocals = 1.
    Exact: sum = 1 iff lcmRange a b = sumScaled (lcmRange a b) a b. --/
def checkK1 (B : Nat) : Bool :=
  (List.range (B - 2)).all fun a =>
    let start := a + 2
    (List.range (B - start - 1)).all fun len =>
      let b := start + len + 1
      let L := lcmRange start b
      sumScaled L start b ≠ L

/-- Kuerschak finite fragment: no run of >= 2 consecutive denominators in [2, B) has
    integral reciprocal sum: L = lcm of the run does not divide the scaled sum. --/
def checkNoIntegerRun (B : Nat) : Bool :=
  (List.range (B - 2)).all fun a =>
    let start := a + 2
    (List.range (B - start - 1)).all fun len =>
      let b := start + len + 1
      let L := lcmRange start b
      sumScaled L start b % L ≠ 0

theorem msl_fmz_erdos289_campaign_001_R003_L1  : checkK1 40 = true ∧ checkNoIntegerRun 40 = true := by decide

-- axiom footprint
#print axioms sumScaled
#print axioms lcmRange
#print axioms checkK1
#print axioms checkNoIntegerRun
#print axioms msl_fmz_erdos289_campaign_001_R003_L1
