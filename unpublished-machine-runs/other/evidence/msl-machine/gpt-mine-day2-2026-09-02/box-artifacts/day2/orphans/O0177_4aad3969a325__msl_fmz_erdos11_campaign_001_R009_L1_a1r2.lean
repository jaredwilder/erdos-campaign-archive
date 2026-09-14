import Mathlib

set_option autoImplicit false


def sqfree (k : Nat) : Bool :=
  (List.range 14).all fun d => k % ((d + 2) * (d + 2)) != 0

def okWit (n l : Nat) : Option (Nat × Nat) :=
  if n > 2 ^ l && sqfree (n - 2 ^ l) then some (n - 2 ^ l, l) else none

def findWit (n : Nat) : Option (Nat × Nat) :=
  (List.range 6).findSome? (okWit n)

def checkAll : Bool :=
  (List.range 127).all fun i => (findWit (3 + 2 * i)).isSome

def witIs (n k l : Nat) : Bool :=
  match findWit n with
  | some (a, b) => a == k && b == l
  | none => false

def certificate : Bool :=
  checkAll && witIs 77 73 2 && witIs 101 97 2

theorem R009_L1_fragment_256 : certificate = true := by decide

theorem msl_fmz_erdos11_campaign_001_R009_L1_a1r2  : certificate = true := by decide

-- axiom footprint
#print axioms sqfree
#print axioms okWit
#print axioms findWit
#print axioms checkAll
#print axioms witIs
#print axioms certificate
#print axioms R009_L1_fragment_256
#print axioms msl_fmz_erdos11_campaign_001_R009_L1_a1r2
