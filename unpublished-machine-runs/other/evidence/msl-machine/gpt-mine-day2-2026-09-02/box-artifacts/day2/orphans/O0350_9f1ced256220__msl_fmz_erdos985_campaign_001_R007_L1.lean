import Mathlib

set_option autoImplicit false


def S3 : Nat -> Nat
  | 0 => 0
  | n+1 => (n+1)*(n+1)*(n+1) + S3 n

def tri : Nat -> Nat
  | n => n * (n+1) / 2

def checkCube (bound : Nat) : Bool :=
  let rec go : Nat -> Bool
    | 0 => true
    | n+1 => (S3 (n+1) == (tri (n+1))^2) && go n
  go bound

theorem msl_fmz_erdos985_campaign_001_R007_L1  : checkCube 50 = true := by decide

-- axiom footprint
#print axioms S3
#print axioms tri
#print axioms checkCube
#print axioms msl_fmz_erdos985_campaign_001_R007_L1
