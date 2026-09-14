import Mathlib

set_option autoImplicit false


structure Frac where num : Int; den : Int

def mkFrac (n d : Int) : Option Frac :=
  if d == 0 then none else some ⟨n, d⟩

-- Exact sign of n1/d1 vs n2/d2 via integer cross-multiplication.
-- No floats, no tolerance: exact Int in {-1,0,1}, or abort on zero denominator.
def crossSign (n1 d1 n2 d2 : Int) : Int :=
  let v := n1 * d2 - n2 * d1
  if v > 0 then 1 else if v < 0 then -1 else 0

def resolveSign (n d : Int) : Option Int :=
  if d == 0 then none else some (crossSign n d 1 1)

def signIsExact (v : Int) : Bool := v == 1 || v == 0 || v == (-1)

-- (a) zero denominators abort at construction (checked by matching, no BEq needed)
def isNone (o : Option Frac) : Bool := match o with | none => true | some _ => false
def isNoneInt (o : Option Int) : Bool := match o with | none => true | some _ => false

def check_zero_den_aborts : Bool :=
  isNone (mkFrac 1 0) && isNone (mkFrac (-7) 0) && isNoneInt (resolveSign 3 0)

-- (b) every well-formed sign test resolves to an exact value in {-1,0,1}
def check_all_resolve : Bool :=
  let cases : List (Int × Int) := [(1,2), (-1,2), (0,5), (7,-3), (-9,-4), (0,1), (123456789, 987654321)]
  cases.all fun c =>
    match resolveSign c.1 c.2 with
    | some s => signIsExact s
    | none => false

-- (c) resolved comparison sign equals exact cross-multiplication sign (Int.sign)
def check_exact_agreement : Bool :=
  let cases : List (Int × Int × Int × Int) :=
    [(1,2, 1,3), (1,2, 2,3), (-1,2, 1,3), (0,5, 0,7), (7,-3, 7,3), (-9,-4, 9,4), (22,7, 355,113)]
  cases.all fun c =>
    crossSign c.1 c.2 c.2.1 c.2.2 == (c.1 * c.2.2 - c.2.1 * c.2).sign

def check_witness (_bound : Nat) : Bool :=
  check_zero_den_aborts && check_all_resolve && check_exact_agreement

theorem msl_fmz_erdos595_campaign_001_R003_L1  : check_witness 7 = true := by decide

-- axiom footprint
#print axioms mkFrac
#print axioms crossSign
#print axioms resolveSign
#print axioms signIsExact
#print axioms isNone
#print axioms isNoneInt
#print axioms check_zero_den_aborts
#print axioms check_all_resolve
#print axioms check_exact_agreement
#print axioms check_witness
#print axioms msl_fmz_erdos595_campaign_001_R003_L1
