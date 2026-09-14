import Mathlib

set_option autoImplicit false


-- total, computable Omega: number of prime factors with multiplicity, by trial division
partial def Omega : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | n =>
      let d := smallestFactor n
      1 + Omega (n / d)
where
  smallestFactor : Nat -> Nat
    | n => go 2 n
  go : Nat -> Nat -> Nat
    | d, n => if d * d > n then n else if n % d == 0 then d else go (d+1) n

def omegaGE3 (n : Nat) : Bool := Omega n >= 3

def checkSmall : Bool :=
  -- within {1..7}: Omega(n) <= 2 exactly for n in {1,2}
  ((List.range 7).map (fun i => i + 1)).all (fun n =>
    (omegaGE3 n) == (n >= 3))
  -- Omega(8) = 3, and 8 in [n, n+6) for n = 3..6
  && omegaGE3 8

def checkCeiling (bound : Nat) : Bool :=
  -- for every 7 <= n <= bound: m = 6*ceil(n/6) satisfies n <= m < n+6 and Omega(m) >= 3
  (List.range (bound - 6)).all (fun d =>
    let n := 7 + d
    let t := (n + 5) / 6
    let m := 6 * t
    n <= m && m < n + 6 && omegaGE3 m)

def checkL1 : Bool := checkSmall && checkCeiling 1000

theorem msl_fmz_erdos891_campaign_001_R010_L1_a1r2  : checkL1 = true := by decide

-- axiom footprint
#print axioms Omega
#print axioms omegaGE3
#print axioms checkSmall
#print axioms checkCeiling
#print axioms checkL1
#print axioms msl_fmz_erdos891_campaign_001_R010_L1_a1r2
