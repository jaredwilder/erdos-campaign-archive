# Attack and Falsification Ledger

## Candidate close under attack

- **C1:** Global Transition Extremality.
- **C2:** Global Theta Minimax.

The close must be abandoned or revised if a genuine bypass, broken premise, orphan region, or post-close theorem is exhibited.

## Attacks already performed

### A1 — Periodic curvature bypass
**Mechanism:** allow nonconstant periodic switch spacings and phase curvatures.  
**Result:** periods 2–4 did not beat the stationary candidate in exploratory optimization.  
**Authority:** computational.  
**Status:** simple periodic bypass weakened, not globally killed.

### A2 — Hidden noncentral cancellation lane
**Mechanism:** insert a never-central coefficient between each pair of central coefficients, with free amplitude/phase, solely to cancel unit-circle peaks.  
**Result:** optimizer drove the lane amplitude toward zero.  
**Authority:** computational.  
**Status:** one explicit dust bypass killed; arbitrary dust handled conceptually by the interpolation dual but not yet globally optimized.

### A3 — Variable central-index gaps
**Mechanism:** periodic pure-skeleton gap patterns such as `(1,2)`, `(1,1,2)`, `(1,2,3)`.  
**Result:** all sampled families were materially worse.  
**Authority:** computational.  
**Status:** simple gap bypass weakened.

### A4 — First-order periodic deformation
**Mechanism:** linearize all periodic perturbations around the two-peak KKT point.  
**Result:** generic first-order descent is obstructed by translation/KKT averaging, but a period-2 soft mode was discovered.  
**Authority:** derived + computational.  
**Status:** valuable falsification of an overly strong rigidity statement.

### A5 — Soft period-2 mode
**Mechanism:** move along the matched alternating scale/phase perturbation.  
**Result:** objective rises approximately `0.54384 a^2` numerically.  
**Authority:** computational.  
**Next hard test:** interval-certify positivity of the second variation on a neighborhood.

### A6 — Arbitrary dust as adversary
**Mechanism:** do not parameterize dust; minimize `L^infty` over all unspecified Fourier coefficients using finite interpolation duality.  
**Result:** arbitrary dust becomes a finite dual optimization once a finite mandatory skeleton window is fixed.  
**Authority:** exact functional-analytic reduction.  
**Status:** conceptual orphan removed; global C1 still open because window length and cocycle dynamics remain coupled.

### A7 — Spectral compression
**Mechanism:** Toeplitz finite sections.  
**Result:** lower bounds rise toward the candidate norm at the stationary profile.  
**Authority:** exact inequality + numerical evaluation.  
**Status:** promising finite-memory route to a global Bellman certificate.

## Strongest current falsification experiments to run next

1. **Finite-window hostile dual search:** jointly optimize admissible skeleton parameters over 3–8 consecutive switches and solve the exact/discretized interpolation dual at each switch. Search specifically for cost below `A_*`.
2. **Aperiodic adversary:** optimize long nonperiodic sequences of `(d_j,s_j,Omega_j)` with free boundary conditions and a terminal cost; no periodicity constraints.
3. **Dust-coupled adversary:** retain a shared global coefficient sequence across adjacent switch windows rather than independently relaxing dust at each switch.
4. **Toeplitz Bellman search:** seek a finite matrix-valued functional `V(state)` proving one-step average/worst-case cost `>=A_*`.
5. **Second-variation interval proof:** isolate the period-2 soft mode and certify positive Hessian after quotienting gauge and KKT-flat directions.
6. **Theta global subdivision:** interval subdivide `[3/2,8] x [0,pi] x theta` and exclude all boxes except the KKT box.

## What would genuinely break C1

Any explicit entire function or admissible infinite cocycle with
\[
\limsup_j\|F_j\|_\infty<A_{\rm SI}
\]
breaks C1 immediately and yields a lower bound better than the entire stationary He–Tang family.

A finite-window numerical dip is **not** enough unless it can be extended to an admissible infinite cocycle or accompanied by a certified periodic/aperiodic construction.

## What would genuinely break C2

Any certified `(K,eps)` with
\[
A(K,eps)<A_*
\]
breaks the candidate theta minimizer. A floating grid value is insufficient; because the apparent gains can be `1e-8` or smaller, all winning claims require reliable angular maximization and interval error control.
