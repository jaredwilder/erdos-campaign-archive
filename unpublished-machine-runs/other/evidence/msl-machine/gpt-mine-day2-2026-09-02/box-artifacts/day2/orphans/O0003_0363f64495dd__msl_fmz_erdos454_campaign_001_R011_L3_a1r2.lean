import Mathlib

set_option autoImplicit false


-- Self-contained: first 12 primes hardcoded as decidable literals (p_k, 1-indexed, p_1=2).
def P : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37]
def pk (k : Nat) : Nat := P.getD (k-1) 0
def fvals (N : Nat) : List Nat := (List.range (N-1)).map (fun i => pk (N + i + 1) + pk (N - i - 1))
def fmin (N : Nat) : Nat := match fvals N with | [] => 0 | l => l.foldl Nat.min (l.head!)
def check (N : Nat) : Bool := fmin N >= 2 * pk N
-- N=5: range 1..4, needs pk(6..9), pk(4..1): all within table of 12 primes.
#eval check 5  -- expect true

theorem msl_fmz_erdos454_campaign_001_R011_L3_a1r2  : check 5 = true := by decide

-- axiom footprint
#print axioms P
#print axioms pk
#print axioms fvals
#print axioms fmin
#print axioms check
#print axioms msl_fmz_erdos454_campaign_001_R011_L3_a1r2
