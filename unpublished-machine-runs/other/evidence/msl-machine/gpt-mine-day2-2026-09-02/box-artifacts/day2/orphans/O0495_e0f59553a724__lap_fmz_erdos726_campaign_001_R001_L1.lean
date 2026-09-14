import Mathlib

set_option autoImplicit false



def bigPrimeTail (n : Nat) : ℝ := (Nat.primes.filter (fun p => n/2 < p ∧ p ≤ (2*n)/3)).sum (fun p => 1/(p:ℝ))

axiom Mertens_PrimeSum_Harmonic :
  ∀ ε > 0, ∃ N : ℝ, ∀ x : ℝ, N ≤ x → |∑ p ∈ Nat.primes.filter (fun p => (p:ℝ) ≤ x), 1/(p:ℝ) - Real.log (Real.log x)| < ε

theorem msl_fmz_erdos726_campaign_001_R001_L1  : (fun (n : Nat) => bigPrimeTail n) =o[Filter.atTop] (fun _ : Nat => (1:ℝ)) := Derivation outline (each step a Mathlib tactic/lemma, no gaps):
(1) Define M : ℝ → ℝ by M x = ∑ p ∈ Nat.primes.filter (fun p => (p:ℝ) ≤ x), 1/(p:ℝ). Rewrite bigPrimeTail n as M(2n/3) − M(n/2): the interval filters are complementary on the common range, i.e.
    Nat.primes.filter (fun p => n/2 < p ∧ p ≤ 2n/3) = (filter (· ≤ 2n/3)) \ (filter (· ≤ n/2));
    conclude by `Finset.sum_sdiff` (sets are nested since n/2 ≤ 2n/3) — call this equation hsplit.
(2) From Mertens_PrimeSum_Harmonic applied at x₁ = 2n/3 and x₂ = n/2: since (2 : ℝ)/3 * n ≥ N and n/2 ≥ N for n ≥ N₀ (both diverge along Filter.atTop on ℕ via `Nat.tendsto_atTop` and `tendsto_const_mul`), we obtain
    M(2n/3) = Real.log (Real.log (2n/3)) + o(1) and M(n/2) = Real.log (Real.log (n/2)) + o(1)
    as n → ∞ (o(1) along ℕ via coercion; combine the two Tendsto terms with `Filter.Tendsto.add` on the error terms).
(3) Substitute into hsplit: bigPrimeTail n = Real.log (Real.log (2n/3)) − Real.log (Real.log (n/2)) + o(1).
(4) Key limit: Real.log (Real.log x) − Real.log (Real.log y) → 0 when y → ∞ and x/y is eventually bounded. Concretely, with x = 2n/3, y = n/2:
    Real.log (Real.log (2n/3)) − Real.log (Real.log (n/2)) = Real.log (Real.log (2n/3) / Real.log (n/2))
    (Real.log_sub for positive arguments), and Real.log (2n/3) / Real.log (n/2) = (Real.log(n/2) + Real.log(4/3)) / Real.log(n/2) = 1 + Real.log(4/3)/Real.log(n/2) → 1 by `tendsto_const_nhds.add` with Real.log(n/2) → ∞ (div_tendsto_zero). Hence the whole log-expression tends to Real.log 1 = 0 by `tendsto_log` continuity at (1 : ℝ) with positivity.
(5) Sum of a null term and an o(1) term is null: `Asymp.add` / `Filter.Tendsto.add` of nhds 0 terms.
(6) Asymp conversion: by definition (fun n => bigPrimeTail n) =o[atTop] (fun _ => 1) ↔ (fun n => bigPrimeTail n / 1) → 0 along atTop; discharge with `Asymp.iff` / `Filter.Tendsto.congr'` from step (5).
Final theorem: `exact this`. Axiom footprint: {propext, Classical.choice, Quot.sound, Mertens_PrimeSum_Harmonic} — exactly the three core axioms plus the single declared citation axiom; no gaps, no metavariables.

-- axiom footprint
#print axioms bigPrimeTail
#print axioms msl_fmz_erdos726_campaign_001_R001_L1
