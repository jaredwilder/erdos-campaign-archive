# Computational Reproduction

## Environment used for this packet

- Python 3.13.5
- NumPy available
- SciPy available
- mpmath available
- `python-flint` / Arb **not installed** in the packet build environment
- Lean **not installed** in the packet build environment

Therefore the bundled calculations are ordinary floating-point/higher-level numerical reconnaissance, not certified interval arithmetic.

## Script 1 — core identity sanity tests

```bash
python code/test_core_identities.py
```

Expected:

```text
PASS: 4 identity families / deterministic finite sanity checks
```

Tested families:
1. gauge invariance of `Omega_j`;
2. Newton future/past skeleton formulas on random finite data;
3. exact cocycle algebra on random finite polynomials;
4. constant-jump substitution ratio invariance at finite radii.

These are tests, not replacements for proofs.

## Script 2 — theta candidate reproduction

```bash
python code/reproduce_theta.py
```

Build output from 2026-08-11:

```text
Erdos #513 theta candidate reproduction -- NONRIGOROUS floating-point
K_exact_float     = 3.5681854422336849
alpha_exact_float = 3.9615431118102280
max |P(theta)|    = 1.709171425067672
argmax theta      = 5.637643778347451
1/A               = 0.585078819674513
endpoint peak      = 1.709171425067672
interior theta     = 0.645541560224373
interior peak      = 1.709171425067672
peak mismatch      = +0.000e+00
KKT success        = True
KKT K              = 3.568185442233683
KKT alpha          = 3.961543111810228
KKT theta          = 0.645541551992596
KKT lambda         = 0.289891149468333
KKT residual inf   = 1.110e-16
KKT candidate A    = 1.709171425067673
KKT candidate 1/A  = 0.585078819674513
```

Toeplitz output:

```text
N= 3  ||T_N||=1.6725917242
N= 4  ||T_N||=1.6933460300
N= 5  ||T_N||=1.6990635554
N=10  ||T_N||=1.7047619161
N=20  ||T_N||=1.7077357508
N=40  ||T_N||=1.7087674456
N=60  ||T_N||=1.7089852974
```

Easy compact-box checks:

```text
K<=1.5 Parseval lower at boundary = 1.750563303422 > A? True
K>=8 alignment lower at boundary = 1.746031746032 > A? True
```

Near-record switch constants:

```text
rho=sqrt(A^2-2) = 0.959826526133
d*s >= -0.5 log(A^2-2) = 0.041002712794
```

## Rigorous lower-bound reproduction

For the published/working lower bound, use an Arb implementation with outward rounding. He–Tang provide a public `python-flint` certification script for their 2026 pair. The July working report states an independent ball-arithmetic check for the improved exact rational pair used here and reports
\[
A<1.709171425067672327265976434342,
\]
so
\[
1/A>0.585078819674513546608465623886.
\]

This packet does not vendor that third-party code. The source URLs are in `07_REFERENCES.md`.

## Required certification before claiming C2

A successful C2 computation must provide all of:

1. exact rational/ball parameter boxes;
2. uniform series tail bounds for function and derivatives;
3. interval certification of the KKT root and uniqueness;
4. global parameter-space subdivision with every noncandidate box eliminated;
5. independent checker or replay log;
6. hash of code, parameters, and output.

A dense angular grid alone is insufficient.
