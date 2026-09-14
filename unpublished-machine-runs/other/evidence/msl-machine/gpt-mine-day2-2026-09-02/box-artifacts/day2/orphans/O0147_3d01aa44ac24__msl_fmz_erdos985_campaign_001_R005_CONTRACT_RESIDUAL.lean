import Mathlib

set_option autoImplicit false


-- Exact, deterministic, fail-closed re-implementation of the residual verifier's sign
-- tests, pure Nat/Bool only (no Real, no Classical, no floats): trial-division primality,
-- exact modular exponentiation, brute-force primitive-root test, per-prime scan.

def isPrime (n : Nat) : Bool :=
  n ≥ 2 && ((List.range (n+1)).filter (fun d => d ≥ 2 && d < n)).all (fun d => n % d != 0)

def modPow : Nat → Nat → Nat → Nat → Nat
  | _, 0, _, acc => acc
  | b, e, m, acc =>
      if e % 2 == 1 then modPow (b*b % m) (e/2) m (acc*b % m)
      else modPow (b*b % m) (e/2) m acc

def isPrimRoot (a p : Nat) : Bool :=
  modPow a (p-1) p 1 == 1 % p
  && ((List.range (p-1)).drop 1).all (fun k => modPow a k p 1 != 1 % p)

def hasPrimitiveRootPrimeBelow (p : Nat) : Bool :=
  ((List.range p).filter isPrime).any (fun q => isPrimRoot q p)

def check_witness : Bool :=
  [3, 5, 7, 11].all (fun p => isPrime p && hasPrimitiveRootPrimeBelow p)

theorem msl_fmz_erdos985_campaign_001_R005_CONTRACT_RESIDUAL  : check_witness = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms modPow
#print axioms isPrimRoot
#print axioms hasPrimitiveRootPrimeBelow
#print axioms check_witness
#print axioms msl_fmz_erdos985_campaign_001_R005_CONTRACT_RESIDUAL
