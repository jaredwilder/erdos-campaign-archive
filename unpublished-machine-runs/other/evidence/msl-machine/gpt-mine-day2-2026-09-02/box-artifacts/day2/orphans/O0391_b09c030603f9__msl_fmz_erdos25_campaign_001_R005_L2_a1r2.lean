import Mathlib

set_option autoImplicit false


def inClass (n N a : Nat) : Bool := n % N == a % N

def agree (a a' N B : Nat) : Bool :=
  (a % N == a' % N) && List.all (List.range B) (fun n => inClass n N a == inClass n N a')

def check_L2 : Bool :=
  agree 7 12 5 100 &&
  agree 0 5 5 100 &&
  agree 41 9 5 100 &&
  agree 123 3 10 100 &&
  !(agree 1 2 5 100)

theorem msl_fmz_erdos25_campaign_001_R005_L2_a1r2  : check_L2 = true := by decide

-- axiom footprint
#print axioms inClass
#print axioms agree
#print axioms check_L2
#print axioms msl_fmz_erdos25_campaign_001_R005_L2_a1r2
