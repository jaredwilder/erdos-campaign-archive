# Formalization and Certification Plan

The fastest credible path is **not** to formalize the entire open problem at once. Formalize the universal reduction stack first, then leave C1 and C2 as sharply typed theorem targets.

## Track A — Lean: universal exact mathematics

Recommended modules, in dependency order:

### A1. `MaximumTermEnvelope`
Definitions:
- coefficient line `L_n(t)=log|a_n|+n*t`;
- maximum-term envelope `H(t)=sup_n L_n(t)` under entire-function hypotheses;
- transition/breakpoint sequence.

Targets:
1. local finiteness of relevant coefficient lines on compact `t` intervals;
2. `H(t)=log mu(e^t,f)`;
3. `H` is convex and affine between consecutive transitions;
4. central index tends to infinity for transcendental entire `f`.

### A2. `EndpointReduction`
Import a theorem or formalize Hadamard three-circles as convexity of `G(t)=log M(e^t,f)`. Then prove
\[
\beta(f)=\liminf_j\mu(R_j,f)/M(R_j,f).
\]

This is the most analysis-heavy early bridge. If mathlib lacks a convenient Hadamard theorem, isolate it as a single imported analytic lemma rather than allowing it to contaminate later algebraic files.

### A3. `SwitchProfile`
Define normalized Laurent/Fourier profile `F_j`. Prove:
- `||F_j||_infty=M(R_j,f)/mu(R_j,f)`;
- `beta(f)=1/limsup ||F_j||_infty`;
- exact cocycle formula.

### A4. `NewtonSkeleton`
Formalize crossing recurrence
\[
\log|a_{\nu_j}|-\log|a_{\nu_{j-1}}|=-d_j\tau_j
\]
and future/past skeleton coefficient formulas.

### A5. `FourierTransitionBound`
Formalize the two active Fourier coefficients, dual test against `1+e^{-idt}`, and prove `||F||_infty>=pi/2`.

Then add:
- deficit identity;
- weighted stability inequality;
- Parseval third-coefficient gap;
- no triple tie below `sqrt 3`;
- scaled spacing law.

### A6. `GaugeAndSubstitution`
Prove:
- phase-curvature gauge invariance;
- `beta(z^m f(c z^d))=beta(f)`.

### A7. `ToeplitzCompression`
Prove finite compression norm bound. Toeplitz norm convergence can be imported as standard if available or proved separately.

### A8. `FourierInterpolationDual`
Formalize the finite-codimension dual formula for mandatory Fourier data. This is likely easier in a finite signed/complex measure or Hahn–Banach framework than via the full dual of `L^infty`; explicitly use weak-* continuous Fourier functionals and finite-dimensional quotient duality.

## Track B — Rigorous numerics: C2

C2 should be attacked with Arb/interval arithmetic before attempting Lean formalization of transcendental numerics.

### B1. Parameter compactification
Prove formally or interval-check the easy global exclusions:
\[
K\notin(3/2,8)\implies A(K,eps)>A_*.
\]
Use conjugation symmetry to reduce phase to a half-circle.

### B2. Uniform theta tail bounds
For each derivative order needed in KKT exclusion, bound
\[
2\sum_{n>N}(2n+1)^mT_n^\ell K^{-T_n}
\]
uniformly on `K>=3/2`.

### B3. Global box subdivision
State variables `(s,alpha,theta)`. For each box:
- upper/lower interval evaluation of `Q=|P|^2`;
- interval derivative signs to eliminate noncritical maxima;
- compare with candidate peak height;
- use KKT necessary conditions to discard parameter boxes.

### B4. Candidate box uniqueness
Use interval Newton/Krawczyk on `(s,alpha,theta,lambda)` for the four KKT equations. Prove a unique solution in a tiny box around the numerical point.

### B5. Global dominance
Prove every parameter box outside the candidate neighborhood has `A>A_candidate`, and every angular maximum within the candidate box is bounded by the certified candidate value.

This proves C2.

## Track C — C1: finite-memory Bellman/dual certificate

This is the highest-value research target.

### State variables
A finite state should include enough mandatory skeleton coefficients around a switch to predict the next window. Candidate coordinates:
\[
(d_j,d_{j+1},x_j,\Omega_j,\ldots)
\]
with
\[
x_j=e^{-d_{j+1}(\tau_{j+1}-\tau_j)}.
\]

### Local cost
For mandatory coefficient vector `b(state)`, define the dust-relaxed local cost
\[
C_N(state)=\mathcal I_{S_N}(b(state))
\]
or spectral lower surrogate
\[
S_N(state)=\|T_N(b(state))\|_{op}.
\]

### Desired Bellman inequality
Find a bounded potential `V` and a constant `A_*` such that for every admissible one-step transition
\[
\max\{C_N(state),\ldots\}+V(next)-V(state)\ge A_*
\]
(or a suitable averaged/log version whose telescoping gives the required limsup lower bound).

A successful finite certificate, together with a rigorous tail/error lemma showing the finite state underestimates the true norm safely, would prove C1.

## Formalization authority ladder

1. **V1:** Python sanity tests for algebraic identities.
2. **V2:** independent high-precision floating reproduction.
3. **V3:** interval/Arb certificates for numerical inequalities.
4. **V4:** finite exact/spectral/dual certificates with independent checker.
5. **V5:** Lean/kernel proof for universal analytic and algebraic reduction; optionally import V4 certificate via a small verified checker.

Do not promote C1/C2 until their respective V4/V5 obligations are satisfied.
