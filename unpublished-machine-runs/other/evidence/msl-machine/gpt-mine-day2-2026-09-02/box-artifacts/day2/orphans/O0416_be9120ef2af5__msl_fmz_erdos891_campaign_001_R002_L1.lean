import Mathlib

set_option autoImplicit false


partial def Omega : Nat -> Nat | 0 => 0 | 1 => 0 | m => if 2 % m == 0 then 0 else 1 + Omega (m / (smallest factor)) -- replaced below by total trial-division version
def omegaCount (m : Nat) : Nat :=
  aux m 2
where
  aux : Nat -> Nat -> Nat
    | 0, _ => 0
    | 1, _ => 0
    | m, d =>
      if d * d > m then 1
      else if m % d == 0 then 1 + aux (m / d) d
      else aux m (d + 1)

def P (k : Nat) : Nat := (List.range (k + 1)).foldl (fun acc i => acc * (Nat.nth (sievePrimes) i)) 1 -- concretely: primes 2,3,5,7,11
def primes5 : List Nat := [2, 3, 5, 7, 11]
def Pk (k : Nat) : Nat := (primes5.take k).foldl (· * ·) 1

def checkK (k bound : Nat) : Bool :=
  let P := Pk k
  (List.range (bound - pow2 k + 1)).all (fun j =>
    let n := pow2 k + j
    (List.range P).any (fun s => omegaCount (n + 1 + s) > k))
where pow2 : Nat -> Nat | 0 => 1 | (n+1) => 2 * pow2 n

def checkAll : Bool :=
  checkK 2 32 && checkK 3 64 && checkK 4 128 && checkK 5 256 && checkK 6 512

theorem msl_fmz_erdos891_campaign_001_R002_L1  : checkAll = true := by decide

-- axiom footprint
#print axioms Omega
#print axioms omegaCount
#print axioms P
#print axioms primes5
#print axioms Pk
#print axioms checkK
#print axioms checkAll
#print axioms msl_fmz_erdos891_campaign_001_R002_L1
