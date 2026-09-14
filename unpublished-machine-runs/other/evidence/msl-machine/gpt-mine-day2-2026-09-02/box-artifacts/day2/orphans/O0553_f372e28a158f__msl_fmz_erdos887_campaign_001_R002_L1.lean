import Mathlib

set_option autoImplicit false


namespace CrossMul

/-- Exact three-way comparison of rationals a/b vs c/d with positive denominators,
    via integer cross-multiplication. Fail-closed: zero denominator gives Abort,
    never a silent order verdict. -/
inductive Cmp | Lt | Eq | Gt | Abort deriving DecidableEq, Repr

def crossCmp (a b c d : Nat) : Cmp :=
  if b = 0 ∨ d = 0 then Cmp.Abort
  else if a * d < c * b then Cmp.Lt
  else if a * d = c * b then Cmp.Eq
  else Cmp.Gt

def isLt : Cmp → Bool | Cmp.Lt => true | _ => false
def isEq : Cmp → Bool | Cmp.Eq => true | _ => false
def isGt : Cmp → Bool | Cmp.Gt => true | _ => false
def isAbort : Cmp → Bool | Cmp.Abort => true | _ => false

/-- Order direction on a concrete instance: 17/5 < 7/2 since 17*2=34 < 35=7*5. -/
def check_order_example : Bool := isLt (crossCmp 17 5 7 2)

/-- Fail-closed guard fires on zero denominators, both sides. -/
def check_abort_zero_den : Bool :=
  isAbort (crossCmp 3 0 1 2) && isAbort (crossCmp 3 4 1 0)

/-- Exactness on ties: 6/4 = 3/2, no tolerance. -/
def check_exact_tie : Bool := isEq (crossCmp 6 4 3 2)

/-- Reversed direction: 7/2 > 17/5. -/
def check_order_fail_direction : Bool := isGt (crossCmp 7 2 17 5)

/-- Exhaustive finite grid: cross-multiplication agrees exactly with the
    integer comparison a*d vs c*b for all numerators < 6 and denominators 1..5. -/
def gridOk : Bool :=
  (List.range 6).all fun a =>
  (List.range 6).all fun c =>
  (List.range' 1 5).all fun b =>
  (List.range' 1 5).all fun d =>
    (isLt (crossCmp a b c d) ↔ (a * d < c * b))
    ∧ (isEq (crossCmp a b c d) ↔ (a * d = c * b))
    ∧ (isGt (crossCmp a b c d) ↔ (a * d > c * b))
    ∧ (isAbort (crossCmp a b c d) = false)

end CrossMul

theorem msl_fmz_erdos887_campaign_001_R002_L1  : CrossMul.check_order_example = true ∧ CrossMul.check_abort_zero_den = true ∧ CrossMul.check_exact_tie = true ∧ CrossMul.check_order_fail_direction = true ∧ CrossMul.gridOk = true := by decide

-- axiom footprint
#print axioms CrossMul.crossCmp
#print axioms CrossMul.isLt
#print axioms CrossMul.isEq
#print axioms CrossMul.isGt
#print axioms CrossMul.isAbort
#print axioms CrossMul.check_order_example
#print axioms CrossMul.check_abort_zero_den
#print axioms CrossMul.check_exact_tie
#print axioms CrossMul.check_order_fail_direction
#print axioms CrossMul.gridOk
#print axioms msl_fmz_erdos887_campaign_001_R002_L1
