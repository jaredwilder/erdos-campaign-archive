import Mathlib

set_option autoImplicit false




open Nat

/-- τ(m) as the exact cardinality of the divisor list. -/
noncomputable def tau (m : ℕ) : ℕ := m.divisors.card

/-- Boolean predicate: L1's divisor bound τ(m) ≤ 2·√m holds for this m.
    decide turns the decidable Nat comparison into a Bool. -/
def tauBoundOk (m : ℕ) : Bool := decide (tau m ≤ 2 * sqrt m)

/-- Exact integer check of L1's load-bearing bound τ(m) ≤ 2·√m
    for all 0 ≤ m ≤ N. Total and computable: List.range + Bool.all. -/
def checkTauBound (N : ℕ) : Bool := (List.range (N + 1)).all tauBoundOk

theorem msl_fmz_erdos826_campaign_001_R002_L1  : checkTauBound 1000 = true := by native_decide

-- axiom footprint
#print axioms tau
#print axioms tauBoundOk
#print axioms checkTauBound
#print axioms msl_fmz_erdos826_campaign_001_R002_L1
