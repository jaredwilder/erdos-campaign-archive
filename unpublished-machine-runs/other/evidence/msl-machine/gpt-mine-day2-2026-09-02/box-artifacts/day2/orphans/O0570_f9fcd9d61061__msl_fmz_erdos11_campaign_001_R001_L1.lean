import Mathlib

set_option autoImplicit false


def sqfree (n : Nat) : Bool :=
  n != 0 && (List.range (n+1)).all (fun d => d*d > n || n % (d*d) != 0)

def witnesses_l0 (n : Nat) : Bool :=
  sqfree (n - 1) && (n - 1) + 1 == n

def check_range (bound : Nat) : Bool :=
  (List.range bound).all (fun m =>
    let n := m + 2
    !(n % 2 == 1 && sqfree (n - 1)) || witnesses_l0 n)

theorem msl_fmz_erdos11_campaign_001_R001_L1  : check_range 40 = true := by decide

-- axiom footprint
#print axioms sqfree
#print axioms witnesses_l0
#print axioms check_range
#print axioms msl_fmz_erdos11_campaign_001_R001_L1
