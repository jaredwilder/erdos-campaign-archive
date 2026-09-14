import Mathlib

set_option autoImplicit false

namespace Day2Wrap


-- Checkable fragment of L1: the RESIDUAL and CLAIM components of the
-- fail-closed certificate spec of packet 432be429739c835b, as total Bool
-- functions. Rationals are pairs (num : Int, den : Nat), den > 0; all
-- comparisons in exact integer arithmetic via cross-multiplication with
-- explicit Nat->Int casts (no floats, no Classical, no Real).

structure Rat where
  num : Int
  den : Nat

def Rat.valid (r : Rat) : Bool := r.den > 0

def Rat.le (a b : Rat) : Bool :=
  a.num * (b.den : Int) <= b.num * (a.den : Int)

structure Interval where
  lo : Rat
  hi : Rat
  hasValue : Bool
  value : Rat

def intervalValid (iv : Interval) : Bool :=
  Rat.valid iv.lo && Rat.valid iv.hi && Rat.valid iv.value
    && Rat.le iv.lo iv.hi
    && (!iv.hasValue || (Rat.le iv.lo iv.value && Rat.le iv.value iv.hi))

def bindsAll (claim : List Nat) (names : List Nat) : Bool :=
  names.all (fun n => claim.contains n)

def claimWellFormed (claim : List Nat) (names : List Nat) : Bool :=
  !claim.isEmpty && bindsAll claim names

def certValid (iv : Interval) (claim : List Nat) (names : List Nat) : Bool :=
  intervalValid iv && claimWellFormed claim names

def goodCert : Interval :=
  { lo := { num := 3, den := 2 }, hi := { num := 3, den := 2 },
    hasValue := true, value := { num := 3, den := 2 } }

def goodInterval : Interval :=
  { lo := { num := 1, den := 2 }, hi := { num := 3, den := 2 },
    hasValue := true, value := { num := 3, den := 4 } }

def badDen : Interval :=
  { lo := { num := 1, den := 0 }, hi := { num := 1, den := 1 },
    hasValue := false, value := { num := 0, den := 1 } }

def badOrder : Interval :=
  { lo := { num := 3, den := 2 }, hi := { num := 1, den := 2 },
    hasValue := false, value := { num := 0, den := 1 } }

def badContain : Interval :=
  { lo := { num := 1, den := 2 }, hi := { num := 3, den := 2 },
    hasValue := true, value := { num := 5, den := 3 } }

def check_spec : Bool :=
  certValid goodCert [1, 2] [1, 2]
  && certValid goodInterval [7] [7]
  && !certValid badDen [1] [1]
  && !certValid badOrder [1] [1]
  && !certValid badContain [1] [1]
  && !certValid goodCert [] [1]
  && !certValid goodCert [1] [1, 2]

theorem msl_fmz_erdos14_campaign_001_R001_L1  : check_spec = true := by decide

end Day2Wrap
-- axiom footprint
#print axioms Day2Wrap.Rat.valid
#print axioms Day2Wrap.Rat.le
#print axioms Day2Wrap.intervalValid
#print axioms Day2Wrap.bindsAll
#print axioms Day2Wrap.claimWellFormed
#print axioms Day2Wrap.certValid
#print axioms Day2Wrap.goodCert
#print axioms Day2Wrap.goodInterval
#print axioms Day2Wrap.badDen
#print axioms Day2Wrap.badOrder
#print axioms Day2Wrap.badContain
#print axioms Day2Wrap.check_spec
#print axioms Day2Wrap.msl_fmz_erdos14_campaign_001_R001_L1
