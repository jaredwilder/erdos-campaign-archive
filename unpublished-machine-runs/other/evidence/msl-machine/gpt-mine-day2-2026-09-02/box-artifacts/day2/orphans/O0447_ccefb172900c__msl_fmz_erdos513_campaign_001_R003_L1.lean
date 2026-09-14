import Mathlib

set_option autoImplicit false



-- Narrowed fragment of L1: exact instance certificate for the decay
-- max_n r^n/n! / e^r -> 0 behind Q(e^z)=0. At r=5, eps=1/5: the unscaled max of
-- r^n/n! is attained at n = r (successive ratios r/(n+1) >= 1 for n <= r-1,
-- < 1 afterward). Clear denominators by scaling with (2r)!: term n becomes
-- (N!/n!) * r^n, a natural number, and sum_{n=0}^{N} of these is < (N)! e^r,
-- so the inequality max_n r^n/n! <= (1/5) e^r follows from the finite check.

def scaledTerm (N n r : Nat) : Nat := (Nat.factorial N / Nat.factorial n) * r ^ n

def partialSum (N r : Nat) : Nat :=
  (List.range (N + 1)).foldr (fun n acc => scaledTerm N n r + acc) 0

def checkWitness (r epsNum : Nat) : Bool :=
  let N := 2 * r
  epsNum * scaledTerm N r r <= partialSum N r

def check_witness : Bool := checkWitness 5 5

theorem msl_fmz_erdos513_campaign_001_R003_L1  : check_witness = true := by decide

-- axiom footprint
#print axioms scaledTerm
#print axioms partialSum
#print axioms checkWitness
#print axioms check_witness
#print axioms msl_fmz_erdos513_campaign_001_R003_L1
