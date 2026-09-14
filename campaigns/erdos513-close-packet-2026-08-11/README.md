# Erdős #513: the maximum-term constant, narrowed to two statements

Erdős asked for the largest constant B such that some transcendental entire function has maximum term μ(r) at least B times its maximum modulus M(r), in the liminf sense. The best published result is B > 0.58507 (He–Tang, 2026, certified with Arb).

This packet makes a specific guess:

> **B = 1/A\* ≈ 0.5850788196745135**, where A\* ≈ 1.709171425067673 is the global minimax of the He–Tang theta family.

It also reduces that guess to two statements, neither of which is proved:

- **C1:** no switching between shapes can beat the best stationary He–Tang shape.
- **C2:** the two-peak equioscillation point found numerically really is the global minimum within that family.

C1 would give B = β_SI, and C2 would give β_SI = 1/A\*. **The problem is still open.**

## What's inside

- `01_CLOSE_MEMO.md`: the reduction, step by step.
- `02_THEOREM_SWEEP.md`: 26 results, each labeled as published, proved here, derived, computational or conjecture. The ones proved here include the Newton-envelope endpoint reduction, a 2/π Fourier obstruction for two active coefficients, and a formula for β on switch profiles.
- `03_ATTACK_AND_FALSIFICATION_LEDGER.md`: what was tried against the guess, and where to aim next.
- `04_FORMALIZATION_PLAN.md` and `lean/Erdos513Targets.lean`: C1 and C2 stated as Lean targets.
- `code/`: reproduces A\* (KKT residual around 1e-16) and tests the core identities. These numbers are not rigorous; the rigorous lower bound is still He–Tang's.

## Check it

```bash
sha256sum -c MANIFEST.sha256
python code/test_core_identities.py
python code/reproduce_theta.py
```

Built August 11, 2026.
