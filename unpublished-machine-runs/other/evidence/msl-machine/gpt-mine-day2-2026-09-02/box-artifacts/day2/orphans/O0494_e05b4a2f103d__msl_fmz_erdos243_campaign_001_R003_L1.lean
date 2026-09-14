import Mathlib

set_option autoImplicit false


def step (a : Nat) : Nat := a * a - a + 1

def block (a : Nat) : Nat -> List Nat
  | 0 => [a]
  | (k+1) => a :: block (step a) k

-- Pointwise kernel of the telescoping identity, all in Nat (no Q, no division):
-- step x - 1 = x * (x - 1)  (so 1/x = 1/(x-1) - 1/(step x - 1) as rationals,
-- since 1/(x-1) - 1/(x(x-1)) = (x-1)/(x(x-1)) = 1/x).
-- Cross-multiplied form of the rational identity, exact in Nat:
-- x * (step x - 1) - x * (x - 1) = (x - 1) * (step x - 1).
def checkPoint (x : Nat) : Bool :=
  step x - 1 == x * (x - 1) &&
  x * (step x - 1) - x * (x - 1) == (x - 1) * (step x - 1)

def checkAll (l : List Nat) : Bool := l.all checkPoint

def block2 : List Nat := block 2 6

def block3 : List Nat := block 3 5

theorem msl_fmz_erdos243_campaign_001_R003_L1  : checkAll block2 = true ∧ checkAll block3 = true ∧ block2.length = 7 ∧ block3.length = 6 := by decide

-- axiom footprint
#print axioms step
#print axioms block
#print axioms checkPoint
#print axioms checkAll
#print axioms block2
#print axioms block3
#print axioms msl_fmz_erdos243_campaign_001_R003_L1
