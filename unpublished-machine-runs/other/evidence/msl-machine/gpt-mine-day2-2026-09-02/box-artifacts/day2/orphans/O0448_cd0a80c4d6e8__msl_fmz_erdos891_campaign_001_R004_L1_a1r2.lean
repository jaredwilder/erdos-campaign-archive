import Mathlib

set_option autoImplicit false


def smallestFactor : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n => go 2 n
where
  go (d : Nat) (n : Nat) : Nat :=
    if d * d > n then n
    else if n % d == 0 then d
    else go (d + 1) n

def omega : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + omega (n / smallestFactor n)

def hasTriple (n : Nat) : Bool := omega n >= 3

def checkWindow (n : Nat) : Bool :=
  (List.range 6).any (fun i => hasTriple (n + i))

def check_L1 (lo hi : Nat) : Bool :=
  (List.range (hi - lo + 1)).all (fun i => checkWindow (lo + i))

theorem msl_fmz_erdos891_campaign_001_R004_L1_a1r2  : check_L1 9 300 = true := by decide

-- axiom footprint
#print axioms smallestFactor
#print axioms omega
#print axioms hasTriple
#print axioms checkWindow
#print axioms check_L1
#print axioms msl_fmz_erdos891_campaign_001_R004_L1_a1r2
