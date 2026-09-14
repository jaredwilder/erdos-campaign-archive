import Mathlib

set_option autoImplicit false



def bigOmega (m : Nat) : Nat := m.factorization.sum fun _ e => e

def P (k : Nat) : Nat := (List.range (k+1) |>.drop 1 |>.map (fun i => (Nat.nth (fun p => Nat.Prime p) i))) |>.prod
-- simpler: primorial of first k primes
def primorial : Nat -> Nat
  | 0 => 1
  | (k+1) => primorial k * (Nat.nth Nat.Prime k)

def windowOK (k n : Nat) : Bool :=
  ((List.range (primorial k)).any fun j => bigOmega (n + j) > k)

def check_base (k nMax : Nat) : Bool :=
  (List.range (nMax - 2 * primorial k + 1)).all
    (fun i => windowOK k (2 * primorial k + i))

def the_check : Bool :=
  check_base 2 2000 && check_base 3 2000 && check_base 4 2000

theorem msl_fmz_erdos891_campaign_001_R007_L1_a1r1  : the_check = true := by decide

-- axiom footprint
#print axioms bigOmega
#print axioms P
#print axioms primorial
#print axioms windowOK
#print axioms check_base
#print axioms the_check
#print axioms msl_fmz_erdos891_campaign_001_R007_L1_a1r1
