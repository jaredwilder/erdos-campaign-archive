import Mathlib

set_option autoImplicit false

namespace Day2Wrap



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

end Day2Wrap
-- axiom footprint
#print axioms Day2Wrap.bigOmega
#print axioms Day2Wrap.P
#print axioms Day2Wrap.primorial
#print axioms Day2Wrap.windowOK
#print axioms Day2Wrap.check_base
#print axioms Day2Wrap.the_check
#print axioms Day2Wrap.msl_fmz_erdos891_campaign_001_R007_L1_a1r1
