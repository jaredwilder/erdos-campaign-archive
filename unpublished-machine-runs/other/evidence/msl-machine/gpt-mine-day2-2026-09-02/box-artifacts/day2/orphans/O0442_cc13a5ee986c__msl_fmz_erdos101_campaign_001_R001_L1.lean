import Mathlib

set_option autoImplicit false


def onLine (a b c : Int × Int) : Bool :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0

def lineSize (pts : List (Int × Int)) (a b : Int × Int) : Nat :=
  (pts.filter (fun c => onLine a b c)).length

def pairsExact (pts : List (Int × Int)) (k : Nat) : Nat :=
  ((pts.flatMap (fun a => pts.filterMap (fun b =>
    if a ≠ b ∧ lineSize pts a b = k then some () else none))).length) / 2

def ptsW : List (Int × Int) := [(0,0), (1,0), (2,0), (3,0), (0,1), (1,2)]

def check : Bool :=
  let n := ptsW.length
  let p2 := pairsExact ptsW 2
  let p4 := pairsExact ptsW 4
  let p5 := pairsExact ptsW 5
  let t2 := p2 / 2
  let t4 := p4 / 6
  n = 6 ∧ p2 = 18 ∧ p4 = 12 ∧ p5 = 0 ∧
  t2 = 9 ∧ t4 = 1 ∧ t4 ≤ t2 ∧ (t2 : ℕ) * 2 ≥ n ∧ t2 ≥ 3 + t4

theorem msl_fmz_erdos101_campaign_001_R001_L1  : check = true := by decide

-- axiom footprint
#print axioms onLine
#print axioms lineSize
#print axioms pairsExact
#print axioms ptsW
#print axioms check
#print axioms msl_fmz_erdos101_campaign_001_R001_L1
