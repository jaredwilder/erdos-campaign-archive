import Mathlib

set_option autoImplicit false


def sqfreeCheck (k : Nat) : Bool :=
  k != 0 && ((List.range 64).all fun d => k % ((d + 2) * (d + 2)) != 0)

def okWit (n l : Nat) : Option (Nat × Nat) :=
  if n - 2 ^ l != 0 && sqfreeCheck (n - 2 ^ l) && (n - 2 ^ l) + 2 ^ l == n then some (n - 2 ^ l, l) else none

def findWit (n : Nat) : Option (Nat × Nat) :=
  (List.range 13).findSome? (okWit n)

def checkAll : Bool :=
  (List.range 2047).all fun i => (findWit (3 + 2 * i)).isSome

def witIs (n k l : Nat) : Bool :=
  match findWit n with
  | some (a, b) => a == k && b == l
  | none => false

def certificate : Bool :=
  checkAll && witIs 77 73 2 && witIs 101 97 2

theorem R009_L1_certificate : certificate = true := by native_decide

theorem msl_fmz_erdos11_campaign_001_R009_L1_a1r1  : certificate = true := by native_decide

-- axiom footprint
#print axioms sqfreeCheck
#print axioms okWit
#print axioms findWit
#print axioms checkAll
#print axioms witIs
#print axioms certificate
#print axioms R009_L1_certificate
#print axioms msl_fmz_erdos11_campaign_001_R009_L1_a1r1
