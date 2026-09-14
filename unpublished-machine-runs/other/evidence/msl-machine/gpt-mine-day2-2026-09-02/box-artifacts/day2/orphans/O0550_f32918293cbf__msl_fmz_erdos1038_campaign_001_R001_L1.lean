import Mathlib

set_option autoImplicit false


inductive Outcome | ok (v : Nat) | failClosed deriving DecidableEq, Repr

def step : Nat -> Outcome
  | 0 => ok 1
  | (n+1) =>
      match step n with
      | failClosed => failClosed
      | ok v =>
          if v % 2 == 0 then
            if 3 * v / 2 > v then ok (3 * v / 2) else failClosed
          else
            if (3 * v + 1) % 2 == 0 then ok ((3 * v + 1) / 2) else failClosed

def noFailClosedUpTo : Nat -> Bool
  | 0 => match step 0 with | failClosed => false | ok _ => true
  | (n+1) => match step (n+1) with
             | failClosed => false
             | ok _ => noFailClosedUpTo n

def checkL1 (N : Nat) : Bool := noFailClosedUpTo N

theorem msl_fmz_erdos1038_campaign_001_R001_L1  : checkL1 12 = true := by decide

-- axiom footprint
#print axioms step
#print axioms noFailClosedUpTo
#print axioms checkL1
#print axioms msl_fmz_erdos1038_campaign_001_R001_L1
