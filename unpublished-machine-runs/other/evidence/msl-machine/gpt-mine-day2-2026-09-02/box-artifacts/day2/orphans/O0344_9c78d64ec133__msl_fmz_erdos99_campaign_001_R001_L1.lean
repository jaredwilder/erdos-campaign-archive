import Mathlib

set_option autoImplicit false


def xmulLess (an bn cn dn : Int) : Bool := an * dn < cn * bn

def xmulAbort (bn dn : Int) : Bool := bn <= 0 || dn <= 0

/-- Decidable soundness probe at one 4-tuple: for positive denominators the Bool
cross-multiplication verdict must equal the exact rational verdict computed by
integer comparison of cross-products (exact, no tolerance); for non-positive
denominators the probe aborts. -/
def probeSound (an bn cn dn : Int) : Bool :=
  if bn > 0 && dn > 0 then
    xmulLess an bn cn dn == (an * dn < cn * bn)
  else xmulAbort bn dn

/-- Witness instances covering sign cases of the comparator. -/
def instances : List (Int × Int × Int × Int) :=
  [(1,2,2,3), (2,3,1,2), (-1,2,0,3), (0,1,0,1), (7,5,7,5), (-3,4,-1,2),
   (5,1,4,1), (100,7,101,7), (-100,7,-101,7), (3,6,1,2), (6,4,9,6), (1,1,1,1),
   (-1,3,1,-3), (9,3,2,1)]

def checkAll : Bool := instances.all (fun t => probeSound t.1 t.2.1 t.2.2.1 t.2.2.2)

def abortCheck : Bool :=
  xmulAbort 0 5 && xmulAbort 5 0 && xmulAbort (-2) 3 && xmulAbort 3 (-2)
    && !(xmulAbort 1 1)

theorem msl_fmz_erdos99_campaign_001_R001_L1  : checkAll = true ∧ abortCheck = true := by decide

-- axiom footprint
#print axioms xmulLess
#print axioms xmulAbort
#print axioms probeSound
#print axioms instances
#print axioms checkAll
#print axioms abortCheck
#print axioms msl_fmz_erdos99_campaign_001_R001_L1
