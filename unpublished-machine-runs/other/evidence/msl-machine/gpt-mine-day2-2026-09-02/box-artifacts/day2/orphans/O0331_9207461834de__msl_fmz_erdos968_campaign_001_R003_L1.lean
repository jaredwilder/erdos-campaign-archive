import Mathlib

set_option autoImplicit false




-- First 11 primes (1-based indexing: p_1 = 2, ..., p_11 = 31)
def primes : List Nat := [2,3,5,7,11,13,17,19,23,29,31]

-- u_n = p_n / n, exactly in ℚ, n ≥ 1
def u (n : Nat) : Rat :=
  match n with
  | (n+1) => ((primes.getD n 0 : Rat) / (n+1 : Rat))

-- Exact rational residual of the telescoping sum Σ_{n=1}^{N} (u_{n+1} − u_n)
-- against its closed form u_{N+1} − u_1; zero residual in ℚ means exact identity.
def residual (N : Nat) : Rat :=
  (List.range N).foldl (fun acc i => acc + (u (i+2) − u (i+1))) 0 − (u (N+1) − u 1)

def checkTelescoping (N : Nat) : Bool := residual N == 0

def check : Bool := checkTelescoping 10

theorem msl_fmz_erdos968_campaign_001_R003_L1  : check = true := by decide

-- axiom footprint
#print axioms primes
#print axioms u
#print axioms residual
#print axioms checkTelescoping
#print axioms check
#print axioms msl_fmz_erdos968_campaign_001_R003_L1
