import Mathlib

set_option autoImplicit false


def Omega (n : Nat) : Nat := (n.factorization.fold (fun _ c acc => acc + c) 0)

def omegaLE (n k : Nat) : Bool := Omega n <= k

def checkWindow (m : Nat) : Bool :=
  -- the 6-block ending at 6t where t = ceil(n/6), i.e. the smallest multiple of 6 >= n
  omegaLE (6 * m) 2 == false  -- Omega(6m) >= 3

def checkSmall : Bool :=
  -- exceptional set: Omega(n) < 3 exactly for n in {1,2} within {1..7}
  ((List.range 7).map (fun i => i + 1)).all (fun n =>
    (omegaLE n 2) == (n == 1 || n == 2))
  -- n=3..6 covered: Omega(8)=3, 8 in [n, n+6) for n in [3,6]
  && (omegaLE 8 2 == false)

def checkCeiling (bound : Nat) : Bool :=
  -- for every n >= 7, n <= 6*ceil(n/6) < n + 6 and Omega(6*ceil(n/6)) >= 3
  (List.range (bound - 6)).all (fun d =>
    let n := 7 + d
    let t := (n + 5) / 6
    let m := 6 * t
    n <= m && m < n + 6 && omegaLE m 2 == false)

def checkL1 : Bool := checkSmall && checkWindow 2 && checkCeiling 1000000

theorem msl_fmz_erdos891_campaign_001_R010_L1_a1r1  : checkL1 = true := by decide

-- axiom footprint
#print axioms Omega
#print axioms omegaLE
#print axioms checkWindow
#print axioms checkSmall
#print axioms checkCeiling
#print axioms checkL1
#print axioms msl_fmz_erdos891_campaign_001_R010_L1_a1r1
