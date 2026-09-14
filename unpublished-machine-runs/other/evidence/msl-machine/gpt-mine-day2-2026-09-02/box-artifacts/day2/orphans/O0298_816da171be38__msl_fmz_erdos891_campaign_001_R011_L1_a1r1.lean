import Mathlib

set_option autoImplicit false


def omAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f+1, n, d =>
    if n ≤ 1 then 0
    else if d * d > n then 1
    else if n % d = 0 then 1 + omAux f (n / d) d
    else omAux f n (d + 1)

def Omega (n : Nat) : Nat := omAux (2 * n + 8) n 2  -- Ω with multiplicity, exact trial division; fuel 2n+8 always suffices

def primes8 : List Nat := [2, 3, 5, 7, 11, 13, 17, 19]
def prim (k : Nat) : Nat := (primes8.take k).prod  -- p_k# for k ≤ 8

def windowHasMult (n L M : Nat) : Bool := (M - n % M) % M < L  -- some multiple of M lies in [n, n+L)

def spacingOK (k : Nat) : Bool :=  -- spacing reduction, checked on ALL residues mod 2^(k+1) (covers every n)
  let M := 2 ^ (k + 1)
  let L := prim k
  (List.range M).all fun r => windowHasMult r L M

def maxOmegaWin (n w : Nat) : Nat :=
  (List.range w).foldl (fun acc i => max acc (Omega (n + i))) 0

def kIneq (k : Nat) : Bool := decide (2 ^ (k + 1) ≤ prim k)
def kOmega (k : Nat) : Bool := decide (Omega (2 ^ (k + 1)) = k + 1)

def k2enum : Bool :=  -- k = 2: exhaustive exact Ω enumeration of [n, n+6), n = 1..16
  (List.range 16).all fun j =>
    let n := j + 1
    let mx := maxOmegaWin n 6
    if n ≤ 2 then decide (mx ≤ 2) else decide (mx > 2)

def k2residues : Bool :=  -- k = 2: periodic mod 8 residue table
  (List.range 8).all fun r =>
    if r == 1 || r == 2 then
      (List.range 6).any fun i => (r + i) % 8 == 4  -- window holds the 4·odd slot
    else
      (List.range 6).any fun i => (r + i) % 8 == 0  -- window holds a multiple of 8

def checkR011 : Bool :=
  (List.range 6).all (fun j => kIneq (j + 3) && kOmega (j + 3))
  && (List.range 6).all (fun j => spacingOK (j + 3))
  && decide (Omega 8 = 3)
  && k2enum
  && k2residues

theorem msl_fmz_erdos891_campaign_001_R011_L1_a1r1  : checkR011 = true := by decide

-- axiom footprint
#print axioms omAux
#print axioms Omega
#print axioms primes8
#print axioms prim
#print axioms windowHasMult
#print axioms spacingOK
#print axioms maxOmegaWin
#print axioms kIneq
#print axioms kOmega
#print axioms k2enum
#print axioms k2residues
#print axioms checkR011
#print axioms msl_fmz_erdos891_campaign_001_R011_L1_a1r1
