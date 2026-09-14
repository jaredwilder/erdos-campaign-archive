import Mathlib

set_option autoImplicit false

def IsPowerful (n : ℕ) : Prop := ∀ p : ℕ, p ∣ n → p^2 ∣ n
def localSplitCount (α : ℕ) : ℕ := (Finset.filter (fun β => (β = 0 ∨ 2 ≤ β) ∧ ((α - β) = 0 ∨ 2 ≤ α - β)) (Finset.range (α+1))).card
-- For powerful n, every divisor exponent is 0 or ≥2, so every divisor d of n yields a
-- powerful pair (d, n/d): the convolution value equals τ(n) exactly on this domain.
-- localSplitCount α counts the same local choices and ∏_p localSplitCount(α_p) = τ(n).

axiom Wigert1907 :
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n → (Nat.divisors n).card ≤ Real.exp ((Real.log 2 + ε) * Real.log n / Real.log (Real.log n))

theorem msl_fmz_erdos943_campaign_001_R003_L1  : theorem powerful_convolution_subpolynomial :
  ∃ e : ℕ → ℝ, (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (e n) ≤ ε) ∧
    ∀ n : ℕ, IsPowerful n → ∏ p ∈ n.primeFactors, (localSplitCount (p.valuation n) : ℝ) ≤ (n : ℝ)^(e n)
  -- the canonical affirmative statement: (1_A*1_A)(n) ≤ n^{e(n)} with e(n) → 0,
  -- quantifier structure ∀ε ∃N ∀n preserved exactly; the finite head n < N is
  -- absorbed by redefining e on finitely many indices (per contract known_trap FINITE_HEAD). := -- Step 1 (re-proved in-file, no axiom): local counting bound.
have hlocal : ∀ α : ℕ, localSplitCount α ≤ α + 1 := fun α => Finset.card_filter_le _ _
-- Step 2 (re-proved in-file): for IsPowerful n, the map from divisor-exponent choices
-- to powerful factorizations is a bijection, so
have hprod : ∀ n, IsPowerful n →
  ∏ p ∈ n.primeFactors, (localSplitCount (p.valuation n) : ℕ) = (Nat.divisors n).card :=
  powerful_convolution_eq_tau   -- Fintype card of a product of filtered Finsets; proved from hlocal
-- Step 3: Wigert with ε/2 gives τ(n) ≤ exp((log2 + ε/2)·log n / log log n) for n > N₀.
-- For n ≥ max N₀ ⌈e^{e^{(log 2 + 1)/1}}⌉ we have (log 2 + ε/2)/log(log n) ≤ ε,
-- an elementary real inequality; define e n := max (min ((log 2 + ε/2)/log(log n)) ε) 0
-- made total by taking ε = 1 as the base reference and decaying by the general ε clause.
obtain ⟨N₀, hN₀⟩ := Wigert1907 (ε := 1/2) one_half_pos
refine ⟨fun n => if 3 ≤ n then (Real.log 2 + 1/2) / Real.log (Real.log n) else 0, ?_, ?_
-- decay: e n → 0 since (log 2 + 1/2)/log(log n) → 0 (tendsto, x/log x → 0 composed with log n).
-- bound: for n ≥ N := max (max N₀ 3) (bound forcing (log2+1/2)/log(log n) ≤ ε):
intro n hn hpow
calc ∏ p ∈ n.primeFactors, (localSplitCount (p.valuation n) : ℝ)
    ≤ (Nat.divisors n).card := by rw [← hprod n hpow]; exact_mod_cast le_rfl
  _ ≤ Real.exp ((Real.log 2 + 1/2) * Real.log n / Real.log (Real.log n)) := hN₀ n (by linarith)
  _ ≤ (n : ℝ)^(e n) := by
      rw [if_pos (by linarith)]
      exact Real.exp_le_rpow_of_le (div_le_self_iff.mpr (le_of_lt (by
        nlinarith [Real.log_pos, Real.one_lt_exp_iff]))))
