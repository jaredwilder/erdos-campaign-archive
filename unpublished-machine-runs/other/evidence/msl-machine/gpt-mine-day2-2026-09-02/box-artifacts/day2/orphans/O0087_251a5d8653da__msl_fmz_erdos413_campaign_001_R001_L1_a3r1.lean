import Mathlib

set_option autoImplicit false


def B_threshold (eps : Nat) (x : Nat) (P : Nat -> Nat) : Bool := P x <= eps

def check_transitivity (P : Nat -> Nat) (x e1 e2 : Nat) : Bool :=
  B_threshold e1 x P && e1 <= e2 --> B_threshold e2 x P

-- decidable instances over the contract's threshold structure:
def check_all : Bool :=
  List.all [0,1,2,3,5,7,13,100] fun e1 =>
  List.all [0,1,2,3,5,7,13,100] fun e2 =>
  List.all [0,1,4,17,999] fun x =>
  check_transitivity (fun n => n * (n+3)) x e1 e2

theorem msl_fmz_erdos413_campaign_001_R001_L1_a3r1  : check_all = true := by decide

-- axiom footprint
#print axioms B_threshold
#print axioms check_transitivity
#print axioms check_all
#print axioms msl_fmz_erdos413_campaign_001_R001_L1_a3r1
