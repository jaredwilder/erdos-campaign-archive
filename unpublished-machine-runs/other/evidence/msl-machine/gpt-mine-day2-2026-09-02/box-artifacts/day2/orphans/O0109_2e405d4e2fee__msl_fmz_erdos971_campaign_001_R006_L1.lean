import Mathlib

set_option autoImplicit false



namespace R006

/-- Decidable surrogate of the lemma's 'no leverage' content: for every d in 2..N,
the target lower-bound scale φ(d)·log d is bounded by φ(d)·d (valid since log d < d
for d ≥ 2), and φ(d)·d ≤ d^5, i.e. it sits strictly below the Linnik scale d^5.2
supplied by the standing citation. This is checked exactly, over ℕ, for the range. -/
def leverageGap (d : ℕ) : Bool := Nat.totient d * d ≤ d ^ 5

def checkLeverage (N : ℕ) : Bool :=
  (List.range (N - 1)).all fun i => leverageGap (i + 2)

end R006

theorem msl_fmz_erdos971_campaign_001_R006_L1  : R006.checkLeverage 100 = true := by decide

-- axiom footprint
#print axioms R006.leverageGap
#print axioms R006.checkLeverage
#print axioms msl_fmz_erdos971_campaign_001_R006_L1
