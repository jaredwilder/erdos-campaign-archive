import Mathlib

set_option autoImplicit false


def divides (d p : Nat) : Bool := p % d == 0

theorem termination_td : ∀ d p : Nat, ∃ n : Nat, d + n = p + 2 := by intro d p; exact ⟨p + 2 - d, Nat.succ_le_succ (Nat.le.intro (Nat.sub_add (p+2) d) ▸ by omega)⟩

def trialDivisionAux (d p : Nat) : Bool :=
  if d * d > p then true
  else if divides d p then false
  else if d + 1 = p + 2 then true else trialDivisionAux (d + 1) p

def isPrimeExact (p : Nat) : Bool :=
  if p < 2 then false else trialDivisionAux 2 p

def in23 (n : Nat) : Bool := n == 2 || n == 3

def allFactorsIn23Aux (d n : Nat) : Bool :=
  if n == 1 then true
  else if d * d > n then in23 n
  else if divides d n then
    in23 d && allFactorsIn23Aux d (n / d)
  else if d + 1 = n + 2 then in23 n else allFactorsIn23Aux (d + 1) n

def isClass1 (p : Nat) : Bool := isPrimeExact p && allFactorsIn23Aux 2 (p + 1)

def check_main : Bool :=
  isPrimeExact 2 && isPrimeExact 3 && isPrimeExact 5 && isPrimeExact 7 &&
  isPrimeExact 23 && !(isPrimeExact 1) && !(isPrimeExact 4) && !(isPrimeExact 25) &&
  isClass1 2 && isClass1 3 && isClass1 5 && isClass1 7 && isClass1 11 &&
  !(isClass1 13) && !(isClass1 19) && !(isClass1 29)

theorem msl_fmz_erdos1055_campaign_001_R002_L1  : check_main = true := by decide

-- axiom footprint
#print axioms divides
#print axioms termination_td
#print axioms trialDivisionAux
#print axioms isPrimeExact
#print axioms in23
#print axioms allFactorsIn23Aux
#print axioms isClass1
#print axioms check_main
#print axioms msl_fmz_erdos1055_campaign_001_R002_L1
