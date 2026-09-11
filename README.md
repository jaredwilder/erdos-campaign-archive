# erdos-campaign-archive

**Eleven of these campaigns carry kernel-checked, sorry-free Lean, including two that refute a
stated conjecture and one that moves a ladder. They are named in
[WHAT-IS-ACTUALLY-IN-HERE.md](WHAT-IS-ACTUALLY-IN-HERE.md) -- a random sample of twenty will
miss all of them.**

**266 campaign directories across 241 distinct Erdos problems.** The complete working record of an
automated attack program, published whole, including the large majority that produced nothing.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## What this is

Every campaign the machine ran against a numbered Erdos problem, with its contract, its route log,
its transcript, its receipts, and whatever it produced. 2,979 files, 215 Lean files, 96 MB.

## What it is not

**Almost none of these closed anything.** A representative audit of the twenty 2026-09-05 close
campaigns found: one proved theorem, one proved tower of necessary conditions, three sets of proved
lemmas or bounds, four refutations that killed their own routes, seven that produced no advance at
all, and two prior-art verdicts.

That ratio is the honest shape of the work and it is why the whole archive is here rather than a
selected subset. A corpus that only contains the campaigns that worked tells you nothing about the
method that produced them.

## The ones that produced something, with their own repositories

| problem | result | repository |
|---|---|---|
| 1084 | prior-art correction to a research-open tag, plus a sealed lower bound | erdos1084-harborth |
| 595 | 27 sorry-free theorems bounding any witness | erdos595-barrier-tower |
| 142 | first exact values of Mathlib's `rothNumberNat` | erdos-close-campaigns |
| 89 | Erdos 1946 bound formalized, with a gap ledger | erdos-close-campaigns |
| 850, 273 | a 4.6e11 exhaustion frontier and a parity-split reduction | erdos-computational-searches |
| 949, 1061, 276, 313, 400, 412, 456, 477, 479, 700, 885, 936, 289 | 79 clean-axiom declarations | erdos-theorems |

Everything else in here is the working record.

## Reading a campaign

Each directory carries some subset of: `contract.json` (the frozen question), `campaign-log.json`,
`transcript.jsonl` (the full reasoning record), `routes/` (attack routes and where they died),
`receipts/`, and `kernel/` where a Lean artifact was produced.

The route logs are the most useful part for anyone studying automated proof search, because they
record **why** each route was abandoned, including the lemmas that were refuted along the way.

## License

Apache-2.0.
