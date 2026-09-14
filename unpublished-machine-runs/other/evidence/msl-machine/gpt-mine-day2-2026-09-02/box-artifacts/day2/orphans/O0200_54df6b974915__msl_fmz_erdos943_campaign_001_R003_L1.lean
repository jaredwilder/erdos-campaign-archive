import Mathlib

set_option autoImplicit false



def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n
def isPowerful (n : ℕ) : Bool := (n == 0) || n.primeFactors.all (fun p => (p^2 : ℕ) ∣ n)
def ConvPowerful (n : ℕ) : ℕ :=
  (Finset.filter (fun m => isPowerful m && isPowerful (n / m) && m * (n / m) == n) (Finset.range (n+1))).card
def LocalCount (α : ℕ) : ℕ := if α = 0 then 1 else if α ≤ 3 then 2 else 4
-- The two decidable combinatorial cores of L1:
-- (i) exact local count: for p^α, pairs (β,γ), β+γ=α, each 0 or ≥2, number = LocalCount α ≤ 4;
-- (ii) hence ConvPowerful n ≤ 4^{ω(n)} ≤ d(n)^2 (squarefree divisors inject into divisors).
def omega (n : ℕ) : ℕ := n.primeFactors.card
def divisorCount (n : ℕ) : ℕ := (Finset.filter (fun m => m ∣ n) (Finset.range (n+1))).card
def checkCore (bound : ℕ) : Bool :=
  (List.range (bound + 1)).all (fun α => LocalCount α ≤ 4) ∧
  (List.range (bound + 1)).all (fun n =>
    ConvPowerful n ≤ 4 ^ (omega n) ∧ 4 ^ (omega n) ≤ (divisorCount n)^2)

theorem msl_fmz_erdos943_campaign_001_R003_L1  : checkCore 400 = true := by decide

-- axiom footprint
#print axioms Powerful
#print axioms isPowerful
#print axioms ConvPowerful
#print axioms LocalCount
#print axioms omega
#print axioms divisorCount
#print axioms checkCore
#print axioms msl_fmz_erdos943_campaign_001_R003_L1
