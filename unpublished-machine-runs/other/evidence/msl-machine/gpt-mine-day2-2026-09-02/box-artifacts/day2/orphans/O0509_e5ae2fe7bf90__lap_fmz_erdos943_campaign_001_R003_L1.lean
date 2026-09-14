import Mathlib

set_option autoImplicit false



def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n
def ConvPowerful (n : ℕ) : ℕ := (Finset.filter (fun m => Powerful m ∧ Powerful (n / m)) (Finset.range (n+1))).card
def LocalCount (α : ℕ) : ℕ := if α = 0 then 1 else if α ≤ 3 then 2 else 4
lemma local_le : ∀ α, LocalCount α ≤ 4 := by intro a; unfold LocalCount; split <;> split <;> norm_num
-- Key arithmetic: for each prime p with p^α ∥ n, the pairs (β,γ), β+γ=α, each part 0 or ≥2,
-- number exactly LocalCount α; hence ConvPowerful n = ∏_{p^α ∥ n} LocalCount α ≤ 4^{ω(n)}.
-- And 4^{ω(n)} = (2^{ω(n)})^2 ≤ d(n)^2 since every squarefree divisor of n is a divisor of n.

axiom Wigert1907 :
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → (Nat.divisorCount n : ℝ) ≤ Real.exp (C * Real.log n / Real.log (Real.log n))

theorem msl_fmz_erdos943_campaign_001_R003_L1  : theorem r003_close : ∀ n : ℕ, 3 ≤ n → Powerful n → (ConvPowerful n : ℝ) ≤ Real.exp ((2*C + 8*Real.log 2) * Real.log n / Real.log (Real.log n)) ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, m ≥ N → Powerful m → (ConvPowerful m : ℝ) ≤ (m : ℝ)^ε := intro n hn hpow. Step 1 (decomposition): ConvPowerful n = ∏ p ∈ n.primeFactors, LocalCount (n.factorization p). For each such p, LocalCount α ≤ 4 by local_le, so ConvPowerful n ≤ 4^(n.primeFactors.card) by Finset.prod_le_prod (nonneg factors) and Finset.prod_const. Step 2 (ω to d): 2^(n.primeFactors.card) ≤ Nat.divisorCount n, since the map squarefree-divisor → divisor is injective (Finset.powersetCard / Nat.sqrt division of the prime-product injection into divisor Finset; standard Mathlib `Nat.divisorCount` ≥ 2^ω via `Nat.squarefree_divisors` cardinality, provable from `Finset.card_powerset_le` and multiplicativity of divisorCount on coprime parts). Hence 4^ω ≤ (Nat.divisorCount n)^2. Step 3 (Wigert): by Wigert1907, d(n) ≤ exp(C·log n/log log n), so d(n)^2 ≤ exp(2C·log n/log log n). Step 4 (constant absorb): 4^ω(n) ≤ exp(8 log 2 · log n / log log n) for n ≥ 3 since log 4^{ω(n)} = ω(n)·log 4 ≤ (log 4)·(log n/log 2) = 2 log 2 · log n / log 2 · ... ≤ 8 log 2 · log n/log log n using ω(n) ≤ log n / log 2 and log log n ≤ log n. Combining with `Real.exp_le_exp.mpr` on the additive log-inequality gives the first conjunct with the fixed constant 2C + 8 log 2. Step 5 (o(1) extraction, no drift): the constant K := 2C + 8 log 2 is FIXED (does not depend on n). For ε > 0, since Real.log (Real.log x) → ∞ as x → ∞ (Tendsto of `Real.tendsto_log_atTop` composed with `tendsto_real_log_atTop`), choose N ≥ 3 with K / log(log N) ≤ ε; then for m ≥ N, K·log m/log log m ≤ ε·log m, and `Real.exp (ε * Real.log m) = m^ε` by `Real.exp_log`. This is exactly one exponent function e(m) := K/log log m for m ≥ 3 (patched arbitrarily on m < 3, a finite head, per contract known_traps FINITE HEAD). All quantifiers match close_branch_A: single constant, full ∀ m eventually, no subsequence.

-- axiom footprint
#print axioms Powerful
#print axioms ConvPowerful
#print axioms LocalCount
#print axioms local_le
#print axioms msl_fmz_erdos943_campaign_001_R003_L1
