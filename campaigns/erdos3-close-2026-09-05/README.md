# Erdős Problem 3 — attack campaign, 2026-09-05

**Target:** `erdos:3` — the Erdős–Turán conjecture on arithmetic progressions ($5,000).
If `A ⊆ ℕ` has `∑_{n∈A} 1/n = ∞`, must `A` contain arbitrarily long arithmetic progressions?

**Outcome: NOT CLOSED.** The problem remains open. What was banked is a sorry-free Lean
development of the *threshold* the problem sits on, kernel-checked end to end.

## What was proved (all sorry-free, clean-room rebuild, `#print axioms` audited)

| Theorem | Content |
|---|---|
| `summable_recip_iff` | `∑_{n∈A} 1/n` converges **iff** `∑_j \|A ∩ [2^j,2^{j+1})\|/2^j` converges — the hypothesis of Erdős 3 restated exactly in dyadic densities |
| `summable_of_log_power_bound` | counting bound `\|A ∩ [0,N)\| ≤ C·N/(log N)^{1+ε}`, `ε>0` ⟹ reciprocal sum converges |
| `divergent_forces_density` | contrapositive: divergence forces the counting function above `N/(log N)^{1+ε}` infinitely often, for every `ε>0` |
| `erdos3_of_quantSzemeredi` | **the reduction**: a quantitative Szemerédi bound `r_k(N) ≪ N/(log N)^{1+ε}` implies Erdős 3 at length `k` |
| `frequently_hasAP_iff_forall` | formalization fidelity: the `∃ᶠ k in atTop` shape of the FormalConjectures statement ⟺ `∀ k` |
| `log_power_threshold_sharp` | **sharpness (dyadic)**: a set with divergent reciprocal sum whose dyadic densities are `≤ 1/(j+1)` |
| `count_critical_le` | explicit: `count critical N ≤ 1 + 4·log2·N/log N` for `N ≥ 4` |
| `log_threshold_sharp_counting` | **sharpness (counting form)**: `count A N ≤ 1 + C·N/log N` for all `N ≥ 4`, yet `∑ 1/n = ∞` |

The last two bracket the threshold exactly:

* counting bound with exponent `> 1` on `log N` ⟹ Erdős 3 settled at that length;
* counting bound with exponent `= 1` ⟹ nothing follows, and a counterexample witnesses it.

For `k ≥ 4` the best unconditional bounds — Gowers' `N/(log log N)^{c_k}`, and the later
quasi-polynomial improvement of Leng–Sah–Sawhney — are still far short of `N/(log N)^{1+ε}`.
The gap the problem asks to close is therefore now quantified rather than asserted.

## Honest limits

* **The conjecture is not proved.** `QuantSzemeredi k` is a *hypothesis* everywhere it appears.
  For `k = 3` it is Bloom–Sisask (2020) — a real theorem, but **not formalized in Mathlib**, so
  `erdos3_three_of_bloomSisask` remains conditional inside Lean.  For `k ≥ 4` it is open.
* **The mathematics is known.** The dyadic characterization, the transfer, and the sharpness
  of the `log`-power threshold are classical (Erdős himself observed the threshold).  What is
  new here is that they are now *kernel-checked* — none of this is in Mathlib, and the
  FormalConjectures file `ErdosProblems/3.lean` carries only the statement plus `sorry`.
* **AP predicate.** The FormalConjectures `Set.IsAPOfLength` lives in `FormalConjecturesUtil`,
  which is not present in this repo's acquisition copy.  These files therefore use a
  self-contained `HasAPOfLength A k := ∃ a d, 0 < d ∧ ∀ i < k, a + i*d ∈ A`, which is the same
  notion (a non-degenerate `k`-term progression inside `A`).

## Layout

```
lean/Erdos3.lean        dyadic characterization, density transfer, the reduction
lean/Erdos3Sharp.lean   the critical set; sharpness in dyadic-density form
lean/Erdos3Count.lean   sharpness in counting-function form, explicit constant
receipts/compile-receipt.json   hashes, exit codes, toolchain, banked/not-banked lists
receipts/axioms.txt             #print axioms output for every headline result
```

## Reproduce

Lean v4.31.0-rc1, Mathlib `919544d4309104b3f19724b0e6e48c701d27948f`.

```bash
LP=$(cd /root/formalizer/proofs && lake env printenv LEAN_PATH)
export LEAN_PATH="$LP:<build-dir>"
for f in Erdos3 Erdos3Sharp Erdos3Count; do lean -o <build-dir>/$f.olean $f.lean; done
```

## Prior estate work checked first

* `oracle/evidence/msl-machine/campaigns/erdos3-campaign-001` — LLM debate transcript only.
  No Lean artifact, no kernel receipt, and it contains at least one false claim (that the
  squares of the primes have a divergent reciprocal sum; `∑ 1/p²` converges).
* `oracle/evidence/encirclement-nuclear/v4-enriched/erdos_3.jsonl` — same debate corpus.
* `oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/3.lean` — statement
  with `sorry`.

Nothing kernel-checked existed for this target before this campaign.
