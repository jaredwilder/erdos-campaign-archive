# Erdős proof-search campaign archive

A research archive of **266 automated proof-search runs across 241 distinct Erdős problems**, comprising **2,979 files and 215 Lean files**. Eleven runs contain kernel-checked, sorry-free Lean, including two refutations of stated conjectures and one improved bound/ladder result; those are indexed in [`WHAT-IS-ACTUALLY-IN-HERE.md`](WHAT-IS-ACTUALLY-IN-HERE.md).

The archive preserves successful, refuted, inconclusive, and null runs together so the proof-search process can be studied from its full outcome distribution rather than only from selected successes.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## Focused homes recovered from this archive

These programs now have problem-specific reading maps, exact source copies,
provenance manifests and their original evidence boundaries:

| Problem | Focused repository |
|---|---|
| #20: sunflower lemmas and constructions | [erdos20-sunflower](https://github.com/jaredwilder/erdos20-sunflower) |
| #592: ordinal Ramsey framework and conditional reductions | [erdos592-ordinal-ramsey](https://github.com/jaredwilder/erdos592-ordinal-ramsey) |
| #593: obligatory hypergraph witnesses and conditional separations | [erdos593-obligatory-hypergraphs](https://github.com/jaredwilder/erdos593-obligatory-hypergraphs) |

The original campaign folders remain here for chronology and provenance.


## What is here

Each research directory preserves the problem statement used for that run, the sequence of attempted approaches, the transcript, verification receipts, and any mathematical objects produced. Across the 96 MB archive are:

- theorem-bearing Lean files;
- exact computations;
- structural lemmas and bounds;
- prior-art findings;
- counterexamples and refutations;
- unsuccessful proof routes;
- runs that produced no mathematical advance.

## Outcome distribution

A representative audit of twenty runs from 2026-09-05 found:

- one proved theorem;
- one proved tower of necessary conditions;
- three sets of proved lemmas or bounds;
- four refutations of proposed routes;
- seven runs with no mathematical advance;
- two prior-art findings.

That denominator matters if the archive is used to study automated proof search. It lets a reader compare productive and unproductive approaches rather than inferring performance from a success-only sample.

## Runs that produced standalone mathematics

| problem | result | repository |
|---|---|---|
| 1084 | prior-art correction to a research-open tag, plus a formalized lower bound | `erdos1084-harborth` |
| 595 | 27 sorry-free barrier theorems | `erdos595-barrier-tower` |
| 142 | first exact values of Mathlib's `rothNumberNat` | `erdos-close-campaigns` |
| 89 | Erdős 1946 bound formalized, with a gap ledger | `erdos-close-campaigns` |
| 850, 273 | a `4.6×10^11` exhaustion frontier and a parity-split reduction | [radical coincidences](https://github.com/jaredwilder/erdos850-radical-coincidences), [covering systems](https://github.com/jaredwilder/erdos273-covering-systems) |
| 949, 1061, 276, 313, 400, 412, 456, 477, 479, 700, 885, 936, 289 | 79 clean-axiom declarations | `erdos-theorems` |

Further mathematics has since been extracted into focused theorem, paper, computation, and archive repositories. This repository remains the underlying research record.

## Reading an individual run

Historical filenames vary, but a directory may contain:

- `contract.json` — the problem statement and frozen assumptions used for the run;
- `campaign-log.json` — chronological run record;
- `transcript.jsonl` — detailed research transcript;
- `routes/` — attempted proof approaches and their outcomes;
- `receipts/` — computational or verification evidence;
- `kernel/` — Lean artifacts where formalization was produced.

The attempted-route records are useful because they preserve **why** an approach was abandoned, including conjectured lemmas that were later falsified. Any surviving theorem or computation should still be read on its own statement and evidence.

## License

Apache-2.0.