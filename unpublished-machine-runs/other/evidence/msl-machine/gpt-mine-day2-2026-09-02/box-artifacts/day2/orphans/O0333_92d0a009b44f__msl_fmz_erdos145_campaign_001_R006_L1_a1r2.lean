import Mathlib

set_option autoImplicit false


-- Möbius function by exact trial factorization.
-- muAux m d: assuming no prime < d divides m with multiplicity issues
-- (guaranteed because we test d*d | m before dividing).
def muAux (m d : Nat) : Int :=
  if d * d > m then
    if m = 1 then 1 else -(1 : Int)
  else if m % (d * d) = 0 then 0
  else if m % d = 0 then -(muAux (m / d) (d + 1))
  else muAux m (d + 1)

def mu (n : Nat) : Int := muAux n 2

-- The exact Möbius-sum reduction N(X) = Σ_{d≤D} μ(d) ⌊X/d²⌋ is not what L1 states;
-- L1 states Σ μ(d)⌊X/d²⌋ with the summand ⌊X/d²⌋. We implement exactly that.
def floorTerm (X d : Nat) : Int := ((X / (d * d)) : Nat)

def S (X D : Nat) : Int :=
  (List.range (D + 1)).foldl
    (fun acc d => acc + mu d * floorTerm X d) 0

def checkN : Bool := S 10000000 3162 = 6079271

theorem msl_fmz_erdos145_campaign_001_R006_L1_a1r2  : checkN = true := by decide

-- axiom footprint
#print axioms muAux
#print axioms mu
#print axioms floorTerm
#print axioms S
#print axioms checkN
#print axioms msl_fmz_erdos145_campaign_001_R006_L1_a1r2
