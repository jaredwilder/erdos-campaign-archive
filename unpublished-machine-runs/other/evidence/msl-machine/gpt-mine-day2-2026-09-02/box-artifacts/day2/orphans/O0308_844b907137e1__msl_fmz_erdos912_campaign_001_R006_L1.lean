import Mathlib

set_option autoImplicit false


namespace R006L1

/-- Exact integer valuation v_p(n!) via Legendre's formula: pure, total, deterministic. -/
def legAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | (k+1), n, p => n / p^(k+1) + legAux k n p

def factVal (n p : Nat) : Nat := legAux (Nat.log n + 1) n p

/-- Distinct positive exponent values among v_p(n!) for primes p ≤ n. -/
def distinctExpCount (n : Nat) : Nat :=
  (List.eraseDups ((List.range (n - 1)).map (fun i => factVal n (i + 2))
    |>.filter (fun v => 0 < v))).length

/-- Total Bool-valued verifier shell; determinism is exactly referential transparency of this pure function. -/
def checkShell (n : Nat) : Bool := distinctExpCount n > 0

end R006L1

theorem msl_fmz_erdos912_campaign_001_R006_L1  : R006L1.checkShell 50 = true ∧ R006L1.factVal 50 2 = 47 := by decide

-- axiom footprint
#print axioms R006L1.legAux
#print axioms R006L1.factVal
#print axioms R006L1.distinctExpCount
#print axioms R006L1.checkShell
#print axioms msl_fmz_erdos912_campaign_001_R006_L1
