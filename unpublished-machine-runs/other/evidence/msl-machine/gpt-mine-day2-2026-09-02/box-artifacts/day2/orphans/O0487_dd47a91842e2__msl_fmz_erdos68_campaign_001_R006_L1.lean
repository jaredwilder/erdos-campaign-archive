import Mathlib

set_option autoImplicit false


def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fac n

def d (n : Nat) : Nat := fac n - 1

/-- q_N = ∏_{k=2}^{N} (k!-1), the common denominator of the N-th partial
    sum of S = Σ_{n≥2} 1/(n!-1) put over this product. -/
def q : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n+1 => d (n+1) * q n

/-- The denominator-growth irrationality template needs the tail
    T_N = Σ_{n>N} 1/(n!-1) < 1/q_N. Since T_N ≥ 1/((N+1)!-1), a
    necessary condition for the template is (N+1)!-1 > q_N. The
    template provably fails at N whenever (N+1)!-1 ≤ q_N, a pure Nat
    comparison in exact integer arithmetic. -/
def templateFailsAt (N : Nat) : Bool := d (N+1) ≤ q N

def check_audit : Bool :=
  (List.range 10).all (fun i => templateFailsAt (i + 5))

theorem msl_fmz_erdos68_campaign_001_R006_L1  : check_audit = true := by decide

-- axiom footprint
#print axioms fac
#print axioms d
#print axioms q
#print axioms templateFailsAt
#print axioms check_audit
#print axioms msl_fmz_erdos68_campaign_001_R006_L1
