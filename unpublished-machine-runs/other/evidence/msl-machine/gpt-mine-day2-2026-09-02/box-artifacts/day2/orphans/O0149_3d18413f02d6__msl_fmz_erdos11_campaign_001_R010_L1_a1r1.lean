import Mathlib

set_option autoImplicit false


def isSquarefree (k : Nat) : Bool := (List.range (k+1)).all (fun d => d > 0 && d < k → d ∣ k → ¬ ((d*d) ∣ k))

def decomposes (n : Nat) : Bool :=
  ((List.range 5).map (fun l => 2 ^ l)).any (fun p =>
    p ≤ n && isSquarefree (n - p))

def oddNs : List Nat := (List.range 26).filterMap (fun m =>
  let n := m + 3
  if n % 2 = 1 then some n else none)

def check_finite_core : Bool :=
  oddNs.length = 13 && oddNs.all decomposes

theorem msl_fmz_erdos11_campaign_001_R010_L1_a1r1  : check_finite_core = true := by decide

-- axiom footprint
#print axioms isSquarefree
#print axioms decomposes
#print axioms oddNs
#print axioms check_finite_core
#print axioms msl_fmz_erdos11_campaign_001_R010_L1_a1r1
