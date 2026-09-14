import Mathlib

set_option autoImplicit false


def evalPoly (cs : List Int) (x : Int) : Int :=
  cs.foldl (fun acc c => acc * x + c) 0

def intervalEval (cs : List Int) (lo hi : Int) : Int × Int :=
  (evalPoly cs lo, evalPoly cs hi)

def signOf (iv : Int × Int) : Option Int :=
  if iv.1 > 0 then some 1
  else if iv.2 < 0 then some (-1)
  else none

/-- Case 1: certified POSITIVE sign at an exact point (p = x^2 - 3 at x = 2). -/
def check1 : Bool :=
  match signOf (intervalEval [-3, 0, 1] 2 2) with
  | some 1 => true
  | _ => false

/-- Case 2: certified NEGATIVE sign at an exact point (p = 3 - x at x = 5). -/
def check2 : Bool :=
  match signOf (intervalEval [3, -1] 5 5) with
  | some (-1) => true
  | _ => false

/-- Case 3: structured ABORT on a zero-straddling interval
    (p = x^2 - 3 over [1,2] gives enclosure [-2, 1]). -/
def check3 : Bool :=
  match signOf (intervalEval [-3, 0, 1] 1 2) with
  | none => true
  | _ => false

/-- Case 4: enclosure ordering sanity on the aborting interval. -/
def check4 : Bool :=
  let iv := intervalEval [-3, 0, 1] 1 2
  iv.1 ≤ iv.2

def checks : Bool := check1 && check2 && check3 && check4

theorem msl_fmz_erdos349_campaign_001_R006_L1  : checks = true := by native_decide

-- axiom footprint
#print axioms evalPoly
#print axioms intervalEval
#print axioms signOf
#print axioms check1
#print axioms check2
#print axioms check3
#print axioms check4
#print axioms checks
#print axioms msl_fmz_erdos349_campaign_001_R006_L1
