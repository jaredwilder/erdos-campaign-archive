import Mathlib

set_option autoImplicit false


def isSquarefree (k : Nat) : Bool :=
  (List.range (k+1)).all (fun d =>
    if d = 0 then true else !(Nat.beq (k / (d*d)) ((k / (d*d)) * (d*d) / (d*d)) && ((d*d) ∣ k)) || !((d*d) ∣ k))

def sqfree (k : Nat) : Bool :=
  (List.range (k+2)).all (fun d =>
    if d ≥ 2 then not (Nat.mod (d*d) 1 = 0 && (k % (d*d) == 0)) else true)

def decomposes (n : Nat) : Bool :=
  ((List.range 5).map (fun l => 2 ^ l)).any (fun p =>
    p ≤ n && sqfree (n - p))

def oddNs : List Nat := (List.range 25).filter (fun n => n % 2 = 1 && n ≥ 3)

def check_finite_core : Bool :=
  oddNs.length == 13 && oddNs.all decomposes

theorem msl_fmz_erdos11_campaign_001_R010_L1_a1r2  : check_finite_core = true := by decide

-- axiom footprint
#print axioms isSquarefree
#print axioms sqfree
#print axioms decomposes
#print axioms oddNs
#print axioms check_finite_core
#print axioms msl_fmz_erdos11_campaign_001_R010_L1_a1r2
