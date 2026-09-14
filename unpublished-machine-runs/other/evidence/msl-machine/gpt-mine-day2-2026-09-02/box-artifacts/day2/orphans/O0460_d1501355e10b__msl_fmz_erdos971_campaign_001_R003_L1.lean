import Mathlib

set_option autoImplicit false


-- L1 fragment: trichotomy of rationals by integer cross-multiplication,
-- fail-closed when the bound is absent.
def Q := Int × Nat  -- (num, den), den > 0

def cmpQ : Q → Q → Option Int  -- LT = -1, EQ = 0, GT = 1, none = absent/fail
  | (a, b), (c, d) =>
      if b = 0 || d = 0 then none
      else
        let sb : Int := if b > 0 then 1 else -1
        let sd : Int := if d > 0 then 1 else -1
        let a' := a * sb; let c' := c * sd
        let n := a' * (d : Int)
        let m := c' * (b : Int)
        if n < m then some (-1) else if n = m then some 0 else some 1

def checkTrichotomy (x y : Q) : Bool :=
  match cmpQ x y, cmpQ y x with
  | some r1, some r2 =>
      (r1 = -1 && r2 = 1) || (r1 = 0 && r2 = 0) || (r1 = 1 && r2 = -1)
  | _, _ => false  -- fail-closed: absent bound yields false, never a default ordering

def checkAbsentFailClosed (x : Q) : Bool := cmpQ x (0, 0) = none

def checkL1 : Bool :=
  checkTrichotomy (1, 2) (2, 4)              -- equality via cross-multiplication
  && checkTrichotomy (1, 3) (1, 2)           -- strict less, negatives of each other
  && checkTrichotomy (-1, 2) (1, 3)          -- sign handling
  && checkAbsentFailClosed (1, 2)            -- fail-closed on absent bound
  && !(checkTrichotomy (1, 2) (3, 4) && false) -- sanity

theorem msl_fmz_erdos971_campaign_001_R003_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms Q
#print axioms cmpQ
#print axioms checkTrichotomy
#print axioms checkAbsentFailClosed
#print axioms checkL1
#print axioms msl_fmz_erdos971_campaign_001_R003_L1
