# Erdős 564 — campaign dossier

**Date:** 2026-09-05 · **Status:** OPEN (not closed by this campaign) · **Prize:** $500
**Statement:** https://www.erdosproblems.com/564 · **Tags:** graph theory, Ramsey theory, hypergraphs

---

## 1. The problem

Let `R_3(n)` be the least `m` such that every 2-colouring of the triples of an `m`-set contains a
monochromatic `n`-set. **Is there `c > 0` with `R_3(n) ≥ 2^(2^(cn))`?**

Formalised in the DeepMind formal-conjectures corpus as
`FormalConjectures/ErdosProblems/564.lean`
(`source_sha256 = df2339f468cf21b0962d2fc1a0989b011c1248a453f7d824c02239aafeb07987`):

```lean
theorem erdos_564 : answer(sorry) ↔
    ∃ c > 0, ∀ᶠ n in atTop, (2 : ℝ)^(2 : ℝ)^(c * n) ≤ hypergraphRamsey 3 n
```

## 2. State of the art (literature — UNPROVED here, cited)

| bound | value | source |
|---|---|---|
| lower, 2 colours | `R_3(n) ≥ 2^{Ω(n²)}` | Erdős–Hajnal; this is essentially the first-moment/union bound, since `C(n,3)/n ~ n²/6` |
| upper, 2 colours | `R_3(n) ≤ 2^{2^{O(n)}}` | Erdős–Rado |
| lower, 3 colours | `R_3(n;3) ≥ 2^{n^{c log n}}` | Conlon–Fox–Sudakov |
| lower, 4 colours | `R_3(n;4) ≥ 2^{2^{cn}}` | Conlon–Fox–Sudakov (stepping-up works with ≥4 colours) |

So the conjectured `2^{2^{cn}}` is **known for 4 colours and open for 2**; the two-colour bounds
differ by a full exponential. The problem is a genuine bottleneck: the Erdős–Hajnal stepping-up
lemma `R_{k+1}(2n+k-4) > 2^{R_k(n)-1}` requires `k ≥ 3`, so *any* improvement to `R_3` propagates
to a tower-height improvement for every `k ≥ 4`.

**Why `k = 2 → 3` fails.** Stepping-up sets `N = 2^m`, identifies vertices with binary strings, and
uses `δ(u,v)` = the top bit at which `u,v` differ, which satisfies `δ(u,w) = max(δ(u,v),δ(v,w))`
and `δ(u,v) ≠ δ(v,w)` for `u<v<w`. To colour triples one must additionally break the
"monotone `δ`-chain" case, and with only two colours there is no colour left to spend on it. With
three or four colours there is — which is exactly the CFS result.

**Not closed by recent work.** arXiv:2606.24198 (2026-06-23, "New Tower-Type Lower Bounds for
Hypergraph Ramsey Numbers") treats `r_k(k+1,k+1)`, a different regime; it does not bear on
`r_3(n,n)`.

## 3. What this campaign did NOT do

It did **not** close 564, and did not improve the `2^{Ω(n²)}` lower bound. Closing it requires a
genuinely new two-colour construction; no such construction was found.

## 4. What this campaign banked

### 4.1 A finding about the formal statement (well-posedness)

`hypergraphRamsey r n := sInf { m | … }` and **`sInf ∅ = 0` in ℕ**. So the formal statement of 564
is only meaningful once one knows the underlying set is nonempty — i.e. modulo the *hypergraph
Ramsey theorem*. If that set were empty, `hypergraphRamsey 3 n = 0` and 564 would be false for a
reason having nothing to do with the mathematics.

**Mathlib (`919544d4`) contains no Ramsey theorem at all** — `grep -ril ramsey Mathlib/` returns
only `Hindman.lean`, `HalesJewett.lean` and three unrelated algebra files; there is no
`Combinatorics/Ramsey`. Neither the graph nor the hypergraph Ramsey theorem is available.

Consequently every lower-bound statement in this campaign carries the nonemptiness hypothesis
**explicitly** rather than silently assuming it. This is the honest form, and it names the missing
prerequisite that any formal attack on 564 must supply first.

### 4.2 Kernel-checked Lean development (sorry-free)

`lean/E564.lean` — 15 theorems, all audited `#print axioms` → `[propext, Classical.choice,
Quot.sound]`, **no `sorryAx`**. Compiled against Mathlib `919544d4`, Lean `4.31.0-rc1`.

| result | content |
|---|---|
| `ramseySet_upward` | admissibility is upward closed (injection transfer) — the fact that makes `sInf` a threshold at all |
| `lt_hypergraphRamsey_iff` | `m < R_r(n) ↔ m carries a witness colouring` (given nonemptiness) |
| `not_mem_ramseySet_of_colouring` | a colouring on *any* type receiving `Fin N` suffices |
| `ramseySet_shrink`, `hypergraphRamsey_shrink` | **`R_r(n) ≤ R_{r+1}(n+1)`** by max-deletion: colour an `(r+1)`-set by `c` applied to it minus its largest element |
| `graphRamsey_le_hypergraphRamsey` | `R_2(n) ≤ R_3(n+1)` — the 564 quantity dominates graph Ramsey |
| `erdos564_of_colourings` | **the reduction an attack uses**: 564 follows from a family of explicit witness colourings, converting the `sInf`-shaped analytic statement into a construction problem |
| `delta`, `delta_spec`, `delta_ne` | the stepping-up `δ` apparatus, realised as `Finset.max` of a symmetric difference under the colex order |
| `col_triple`, `mono_card_le` | monochromatic sets in the construction have `≤ m+2` elements |
| `not_mem_ramseySet_pow` | **`2^m ∉ RamseySet 3 (m+3)`** — unconditional, no hypotheses |
| `pow_lt_hypergraphRamsey` | **`R_3(n) > 2^(n-3)`** (given nonemptiness) |

**The construction.** Host = subsets of `Fin m` under the colexicographic order (so `|host| = 2^m`).
`δ(u,v)` := the largest coordinate at which `u,v` differ = `(u ∆ v).max`; colex is *defined* by
which side that coordinate falls on, which is what makes `delta_spec` available from Mathlib's
`Finset.Colex.lt_iff_max'_mem`. Colour a triple `u<v<w` by `δ(u,v) < δ(v,w)`. The single real
lemma is `delta_ne`: for `u<v<w` the two `δ`s differ, because the first lies in `v` and the second
does not. Hence along a monochromatic set the consecutive `δ`s are *strictly* monotone, so a
monochromatic set has at most `m+2` elements.

This bound (`2^{n-3}`) is **weaker than the literature's `2^{Ω(n²)}`**. Its value is that it is
explicit, unconditional, kernel-checked — the first formal lower bound of any kind on the 564
quantity — and that it builds the `δ` machinery the problem revolves around, and exercises
`erdos564_of_colourings` end-to-end.

### 4.3 SAT: verified witness for `r_3(4) ≥ 13`

- `sat/gen_r3.py` emits the DIMACS: variable per triple, two 4-clauses per `n`-subset.
- `N=12, n=4`: **SATISFIABLE** (cadical, `sat/N12_cadical.log`).
- `sat/verify_witness.py` re-checks the model **independently of the solver**: rebuilds the
  colouring and brute-forces all 495 4-subsets → `sat/verify_N12.txt`:
  *"VERIFIED: 2-colouring of the 220 triples of [12] (110 red / 110 blue) has NO monochromatic
  4-set … therefore r_3(4) > 12."*
- `N=13, n=4` (the matching UNSAT, which would give `r_3(4) = 13`): launched with a 7200 s budget,
  **not finished at time of writing** — see `receipts/RECEIPTS.json`. `r_3(4) = 13` is in any case
  a known published value (McKay–Radziszowski 1991); the reproduction is a receipt, not a record.
  A first attempt emitting a DRAT proof was aborted by the operator agent because the proof file
  grew 2 GB in 7 minutes and threatened the box's disk; the rerun logs no proof, so an UNSAT
  result from it would be solver-trusted, not DRAT-checked. **Marked UNPROVED unless/until it
  terminates and is re-run with proof logging on a machine with the disk for it.**

## 5. Reproduction

```bash
# Lean (rented box; Mathlib 919544d4, Lean 4.31.0-rc1)
scp lean/E564.lean root@<box>:/root/e564/lean/
ssh root@<box> 'export PATH=/root/.elan/bin:$PATH; cd /root/formalizer/proofs && \
  lake env lean /root/e564/lean/E564.lean'          # exit 0, no output
# axiom audit: append #print axioms lines, recompile; expect no sorryAx

# SAT
python sat/gen_r3.py 12 4 sat/r3_4_N12.cnf
cadical -q sat/r3_4_N12.cnf > sat/N12_cadical.log
python sat/verify_witness.py sat/N12_cadical.log 12 4
```

## 6. Next moves, in priority order

1. **Formalise the hypergraph Ramsey theorem** (`(RamseySet r n).Nonempty`). It is absent from
   Mathlib, it is the prerequisite for *every* numeric statement about `hypergraphRamsey`, and it
   discharges the hypothesis in six of the results above. Erdős–Rado induction on `r`.
2. **Formalise the `2^{Ω(n²)}` union bound** — the current world-record lower bound for 564.
   Statement: if `C(N,n)·2^(1-C(n,3)) < 1` then `N ∉ RamseySet 3 n`. The obstacle is Lean
   cardinality API for function spaces constant on a sub-domain, not the mathematics.
3. Only then is an attack on the double-exponential itself worth compute: it needs a new
   two-colour construction, and the `δ` apparatus in `E564.lean §Construction` is the place to
   build it.
