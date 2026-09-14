import Mathlib

set_option autoImplicit false


def parityCheck (n : Nat) : Bool := (n * (n + 1)) % 2 == 0

def fact : Nat -> Nat
  | 0 => 1
  | (n+1) => (n+1) * fact n

def checkInstance (n : Nat) (as : List Nat) : Bool :=
  match as with
  | [] => false
  | a1 :: rest => (a1 <= n - 1) && rest.all (fun a => a >= 2) && rest.foldl (fun acc a => acc * fact a) (fact a1) == fact n

-- Narrowed fragment: parity on a small decidable range, one exact instance.
def fullCheck : Bool :=
  (List.range 40).all parityCheck
  && checkInstance 5 [4, 3]

theorem msl_fmz_erdos373_campaign_001_R002_L1  : fullCheck = true := by decide

-- axiom footprint
#print axioms parityCheck
#print axioms fact
#print axioms checkInstance
#print axioms fullCheck
#print axioms msl_fmz_erdos373_campaign_001_R002_L1
