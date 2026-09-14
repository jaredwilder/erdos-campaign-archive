import Mathlib

set_option autoImplicit false


def isPow2 (m : Nat) : Bool := m == 2 ^ m.log2 && m > 0
def powful (m : Nat) : Bool :=
  m > 0 && (List.range (m+1)).any (fun a => a > 1 && m % a == 0 && (m / a) % a == 0)
def census : List Nat :=
  (List.range 10).filter (fun n =>
    powful (2^n - 1) || powful (2^n + 1) || powful (n! - 1) || powful (n! + 1))
def check_census : Bool := census == [3, 4, 5, 7]

theorem msl_fmz_erdos936_campaign_001_R006_L1_a1r1  : check_census = true := by decide

-- axiom footprint
#print axioms isPow2
#print axioms powful
#print axioms census
#print axioms check_census
#print axioms msl_fmz_erdos936_campaign_001_R006_L1_a1r1
