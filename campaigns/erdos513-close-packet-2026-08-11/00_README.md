# Erdős Problem #513 — External Close / Formalization Packet

**Build date:** 2026-08-11  
**Campaign state at export:** **TCR-3 — ENCIRCLEMENT**  
**Original objective:** determine
\[
B=\sup_f\liminf_{r\to\infty}\frac{\mu(r,f)}{M(r,f)}
\]
over transcendental entire functions.

This packet is deliberately split into three authority classes:

- **THEOREM / PUBLISHED:** proved mathematics or an exact derivation supplied with proof.
- **COMPUTATIONAL RECONNAISSANCE:** reproducible numerical evidence, not a proof.
- **CLOSE OBLIGATION:** explicit unproved statement whose proof would advance/close the program.

The packet does **not** assert that Erdős #513 is solved. It is designed so an external mathematician, interval-arithmetic verifier, or formalizer can attack the current close without reconstructing twenty rounds of chat.

## The close in one sentence

The campaign has reduced the problem to two explicit obligations:

1. **C1 — Global Transition Extremality:** every admissible normalized switch cocycle has asymptotic worst switch norm at least the best stationary He–Tang/theta norm.
2. **C2 — Global Theta Minimax:** the observed two-peak KKT/equioscillation point is the global minimizer within the He–Tang scaling-identity family.

If C1 and C2 are proved, then
\[
B=A_\dagger^{-1}\approx 0.5850788196745135.
\]

C1 is the conceptual wall. C2 looks suited to compact interval certification.

## Run first

```bash
python code/test_core_identities.py
python code/reproduce_theta.py
```

Expected first line from the identity test:

```text
PASS: 4 identity families / deterministic finite sanity checks
```

`reproduce_theta.py` is explicitly **NONRIGOROUS** floating-point reconnaissance. It reproduces the candidate geometry and Toeplitz lower-bound hierarchy; it does not replace Arb/interval certification.

## Files

- `01_CLOSE_MEMO.md` — exact close statement and closure chain.
- `02_THEOREM_SWEEP.md` — full theorem/claim ledger from Rounds 1–20.
- `03_ATTACK_AND_FALSIFICATION_LEDGER.md` — killed routes, surviving bypasses, and what would falsify the close.
- `04_FORMALIZATION_PLAN.md` — Lean/interval decomposition with dependency order.
- `05_COMPUTATIONAL_REPRODUCTION.md` — numerical claims, scripts, and expected outputs.
- `06_TERMINAL_CONTRACT.md` — doctrine-compatible terminal-close contract for the next saturation phase.
- `07_REFERENCES.md` — public source ledger checked 2026-08-11.
- `code/` — deterministic sanity/reproduction scripts.
- `lean/Erdos513Targets.lean` — unproved Lean target skeleton, intentionally marked with `sorry`.
- `MANIFEST.sha256` — file hashes for handoff integrity.

## Current public baseline

He–Tang prove the exact scaling-family reduction and certify `B > 0.58507` (arXiv:2602.12217). A July 2026 working report gives an explicit rational parameter pair and independent Arb-style certification of

\[
B>0.585078819674,
\]

while explicitly stating that the exact value remains open. The public optimization-constants page currently records `0.5850788` as the lower bound.

The exact rational parameters used in this packet are

\[
K=\frac{713637088446737}{200000000000000},\qquad
\alpha=\frac{990385777952557}{250000000000000}.
\]
