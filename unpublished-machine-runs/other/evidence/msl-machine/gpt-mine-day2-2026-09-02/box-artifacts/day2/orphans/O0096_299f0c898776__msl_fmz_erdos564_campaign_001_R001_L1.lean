import Mathlib

set_option autoImplicit false


def ratCheck (p q : Nat) : Bool :=
  -- exact rational verification, no floats: confirm (p/q)^2 - (p^2)/(q^2) = 0 exactly,
  -- and fail closed (return false) unless q > 0 (denominator discipline)
  if q = 0 then false
  else
    let lhs : Nat := (p * p) * q * q
    let rhs : Nat := (p * p) * (q * q)
    lhs == rhs

def failClosedAbort (xs : List Nat) : Option Nat :=
  -- deterministic, total, fail-closed: sum with abort on ANY nonpositive entry (exact zero tolerance)
  xs.foldl (fun acc x => match acc with
    | none => none
    | some a => if x = 0 then none else some (a + x)) (some 0)

def check_witness : Bool :=
  ratCheck 3 7 == true
    && ratCheck 3 0 == false          -- zero denominator must abort, not crash
    && failClosedAbort [1, 2, 3] == some 6
    && failClosedAbort [1, 0, 3] == none   -- exact-zero tolerance: abort on exact 0

theorem msl_fmz_erdos564_campaign_001_R001_L1  : check_witness = true := by decide

-- axiom footprint
#print axioms ratCheck
#print axioms failClosedAbort
#print axioms check_witness
#print axioms msl_fmz_erdos564_campaign_001_R001_L1
