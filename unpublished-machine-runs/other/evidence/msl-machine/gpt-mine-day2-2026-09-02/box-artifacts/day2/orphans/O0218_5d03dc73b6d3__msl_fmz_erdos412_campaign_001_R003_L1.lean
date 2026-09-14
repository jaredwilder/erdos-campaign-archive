import Mathlib

set_option autoImplicit false


def divides (d n : Nat) : Bool := n % d == 0

def sigma (n : Nat) : Nat :=
  (List.range (n + 1)).filter (fun d => divides d n) |>.sum

def check_bound (b : Nat) : Bool :=
  (List.range (b - 1)).all (fun i =>
    let n := i + 2
    sigma n >= n + 1)

-- sigma n sums d over 0..n with d | n; only 1..n divide n ≥ 1, so sigma n = σ(n).
-- check_bound b verifies σ(n) ≥ n + 1 for every 2 ≤ n ≤ b by exact Nat arithmetic.
-- Bounds kept small (b = 60) so that `decide` terminates by kernel evaluation.

theorem msl_fmz_erdos412_campaign_001_R003_L1  : check_bound 60 = true := by decide

-- axiom footprint
#print axioms divides
#print axioms sigma
#print axioms check_bound
#print axioms msl_fmz_erdos412_campaign_001_R003_L1
