import Mathlib

set_option autoImplicit false


partial def lpAux (n : Nat) (d : Nat) : Nat :=
  if d * d > n then n
  else if n % d == 0 then lpAux (n / d) d
  else lpAux n (d + 1)
termination_by (if n % d == 0 then n / d else n, d) => (by
  simp only [if_pos]
  split
  · exact Nat.div_lt_self (by omega) (by omega)
  · omega)

def lpFac (n : Nat) : Nat := lpAux n 2

def checkEndpoint (n : Nat) : Bool :=
  -- k=1 arm: P(C(n,1)) = P(n) >= min(n, 1^(1+c)) = 1
  (lpFac n >= 1)
  -- k=n-1 arm: P(C(n,n-1)) = P(n) >= min(n-k+1, k^(1+c)) = min(2, (n-1)^(1+c))
  -- worst case over c>0 is c -> 0, so bound is min(2, n-1); for n>=2 this is <= 2,
  -- and any prime factor of n is >= 2, so it suffices to check lpFac n >= 2
  && (lpFac n >= 2)

def checkRange (N : Nat) : Bool :=
  (List.range (N - 1)).all (fun i => checkEndpoint (i + 2))

theorem msl_fmz_erdos683_campaign_001_R002_L1  : checkRange 60 = true := by decide

-- axiom footprint
#print axioms lpAux
#print axioms lpFac
#print axioms checkEndpoint
#print axioms checkRange
#print axioms msl_fmz_erdos683_campaign_001_R002_L1
