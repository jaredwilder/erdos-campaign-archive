import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  n ≥ 2 && (List.range n).all (fun d => d < 2 || d * d > n || n % d != 0)

def primesUpTo (N : Nat) : List Nat := (List.range (N + 1)).filter isPrime

def primorial (k : Nat) : Nat :=
  ((primesUpTo 50).take k).foldl (fun a b => a * b) 1

def omegaF (fuel n : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | (fuel + 1) =>
    if n ≤ 1 then 0
    else
      match ((List.range (n + 1)).filter (fun d => d ≥ 2)).find? (fun d => n % d == 0) with
      | some d => 1 + omegaF fuel (n / d)
      | none => 0

def omega (n : Nat) : Nat := omegaF (n + 1) n

-- L1's witness for window [n, n + P_k): the least multiple of 2^k that is >= n.
-- Lemma asserts: it lies inside the window (needs P_k >= 2^k) and has Omega >= k+1.
def witnessOK (k n : Nat) : Bool :=
  let P := primorial k
  let two := 2 ^ k
  let q := (n + two - 1) / two
  let m := q * two
  primorial k ≥ two && m < n + P && omega m ≥ k + 1 && omega m > k

def checkL1 : Bool :=
  (List.range 4).all (fun i =>
    let k := i + 2
    (List.range 10).all (fun j => witnessOK k (2 ^ k + 1 + j)))

theorem msl_fmz_erdos891_campaign_001_R005_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms primesUpTo
#print axioms primorial
#print axioms omegaF
#print axioms omega
#print axioms witnessOK
#print axioms checkL1
#print axioms msl_fmz_erdos891_campaign_001_R005_L1
