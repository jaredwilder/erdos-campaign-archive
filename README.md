# erdos-campaign-archive

**266 campaign directories across 241 distinct Erdős problems: 2,979 files, 215 Lean files, and a complete working record of an automated attack program.** Eleven campaigns carry kernel-checked, sorry-free Lean, including two that refute a stated conjecture and one that moves a ladder; they are indexed in [WHAT-IS-ACTUALLY-IN-HERE.md](WHAT-IS-ACTUALLY-IN-HERE.md).

The archive publishes successful, refuted, inconclusive, and null campaigns together so the method can be studied against its full outcome distribution rather than only its wins.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## What is here

Every campaign the machine ran against a numbered Erdős problem, with its contract, route log, transcript, receipts, and whatever mathematical object it produced. The archive is 96 MB and includes theorem-bearing Lean, exact computations, structural lemmas, prior-art verdicts, refutations, dead routes, and campaigns that produced no advance.

## Outcome distribution

A representative audit of twenty 2026-09-05 close campaigns found:

- one proved theorem;
- one proved tower of necessary conditions;
- three sets of proved lemmas or bounds;
- four refutations that killed their own routes;
- seven campaigns producing no mathematical advance;
- two prior-art verdicts.

That distribution is part of the scientific content of the archive. Publishing the full denominator makes it possible to study which routes worked, which failed, and how often, rather than inferring a method's performance from a selected success set.

## Campaigns that produced standalone mathematics

| problem | result | repository |
|---|---|---|
| 1084 | prior-art correction to a research-open tag, plus a sealed lower bound | `erdos1084-harborth` |
| 595 | 27 sorry-free theorems bounding any witness | `erdos595-barrier-tower` |
| 142 | first exact values of Mathlib's `rothNumberNat` | `erdos-close-campaigns` |
| 89 | Erdős 1946 bound formalized, with a gap ledger | `erdos-close-campaigns` |
| 850, 273 | a 4.6e11 exhaustion frontier and a parity-split reduction | `erdos-computational-searches` |
| 949, 1061, 276, 313, 400, 412, 456, 477, 479, 700, 885, 936, 289 | 79 clean-axiom declarations | `erdos-theorems` |

Additional mathematics has since been extracted into the release's focused theorem, paper, computation, and ore repositories; this archive remains the provenance-level working record.

## Reading a campaign

Each directory carries some subset of: `contract.json` (the frozen question), `campaign-log.json`, `transcript.jsonl` (the full reasoning record), `routes/` (attack routes and where they died), `receipts/`, and `kernel/` where a Lean artifact was produced.

The route logs are especially useful for studying automated proof search because they record **why** a route was abandoned, including lemmas falsified during the campaign. The mathematical status of any surviving object is determined by that object's statement and evidence, not by the fact that its parent campaign targeted a larger open problem.

## License

Apache-2.0.
