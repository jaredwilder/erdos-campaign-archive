import Mathlib

set_option autoImplicit false


def ind1 (n p : Nat) : Bool := let r := n % p; r > p / 2 && r < p

def ind2 (n p : Nat) : Bool := (2 * n / p) % 2 == 1

/-- The termwise indicator identity of L1, checked for every n <= N and every
    odd prime p <= n. For odd p, n % p = p/2 is impossible (p/2 non-integer),
    and with r := n % p: ind2 holds iff floor(2r/p) is odd iff 2r > p iff
    r > p/2 iff ind1 holds; both indicators are unchanged by subtracting the
    even multiple 2*floor(n/p)*p from n. p = 2 is the sole boundary case
    (n % 2 = 1 = p/2) and is deliberately excluded. -/
def check (N : Nat) : Bool :=
  (List.range (N + 1)).all fun n =>
    ((List.range (n + 1)).filter (fun p => p > 2 && p % 2 == 1)).all fun p =>
      ind1 n p == ind2 n p

theorem msl_fmz_erdos726_campaign_001_R005_L1  : check 120 = true := by decide

-- axiom footprint
#print axioms ind1
#print axioms ind2
#print axioms check
#print axioms msl_fmz_erdos726_campaign_001_R005_L1
