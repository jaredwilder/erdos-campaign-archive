# Full Theorem Sweep — Rounds 1–20

This ledger distinguishes exact mathematics from numerical reconnaissance and conjectural close claims.

Legend:

- **PUBLISHED** — directly supported by cited literature.
- **PROVED-HERE** — elementary/exact derivation supplied in the campaign; should be independently checked/formalized.
- **DERIVED-TARGET** — derivation appears sound but deserves explicit formal proof before bank promotion.
- **COMPUTATIONAL** — numerical evidence only.
- **CONJECTURE** — unproved close statement.

## A. Published baseline

### P1 — He–Tang scaling family is entire and has exact beta formula — PUBLISHED
For
\[
f_{K,\varepsilon}(z)=\sum_{n\ge0}\varepsilon^{n(n-1)/2}K^{-n(n+1)/2}z^n,
\]
with `K>1`, `|eps|=1`, He–Tang prove `f` transcendental entire and
\[
\beta(f_{K,\varepsilon})=
1/A(K,\varepsilon),
\quad
A=\max_{|z|=1}|k_{K,\varepsilon}(z)|.
\]

### P2 — He–Tang scaling identity — PUBLISHED
\[
k_{K,\varepsilon}(Kz)=z\,k_{K,\varepsilon}(\varepsilon z).
\]

### P3 — He–Tang cosine representation — PUBLISHED
\[
e^{i\theta}k_{K,\varepsilon}(\varepsilon e^{2i\theta})
=2\sum_{n\ge0}\frac{\varepsilon^{T_n}}{K^{T_n}}
\cos((2n+1)\theta).
\]

### P4 — Best scaling-family constant is a theta minimax — PUBLISHED
\[
\beta_{\rm SI}=1/\inf_{K,\varepsilon}A(K,\varepsilon),
\quad B\ge\beta_{\rm SI}.
\]

## B. Switch geometry and endpoint reduction

### T1 — Programmable switch-radius family — PROVED-HERE
Given `R_n` strictly increasing to infinity and unit phases `u_n`, define
\[
a_0=1,\qquad a_n=a_{n-1}u_n/R_n.
\]
Then the resulting power series is transcendental entire, and
\[
\frac{|a_n|r^n}{|a_{n-1}|r^{n-1}}=r/R_n.
\]
Hence the unique maximum term on `(R_m,R_{m+1})` is `m`, while `m-1,m` tie at `R_m`.

### T2 — Endpoint reduction for the programmable family — PROVED-HERE
On each switch interval, `log mu` is affine and `log M` is convex, so `log(mu/M)` is concave and its minimum occurs at an endpoint.

### T3 — Universal endpoint reduction — PROVED-HERE
For an arbitrary transcendental entire function, let `tau_j` be the breakpoints of the Newton upper envelope
\[
H(t)=\max_n(\log|a_n|+nt).
\]
Then
\[
\beta(f)=\liminf_j\frac{\mu(e^{\tau_j},f)}{M(e^{\tau_j},f)}.
\]
Formalization note: prove local finiteness of active coefficient lines on compact `t`-intervals and existence of infinitely many transitions for a transcendental entire function.

### T4 — Switch-profile beta formula — PROVED-HERE
For normalized transition profiles `F_j`,
\[
\beta(f)=1/\limsup_j\|F_j\|_\infty.
\]

## C. Fourier obstruction and stability

### T5 — Two-active-coefficient `2/pi` inequality — PROVED-HERE
At a transition with two active frequencies `p<q`, phase/angle normalization gives Fourier coefficients `c_p=c_q=1`. Then
\[
2\le\|F\|_\infty\frac1{2\pi}
\int|1+e^{-i(q-p)t}|dt
=\|F\|_\infty\frac4\pi,
\]
so
\[
\|F\|_\infty\ge\pi/2,
\qquad \mu/M\le2/\pi.
\]

### T6 — Equality anatomy for T5 — DERIVED-TARGET
Equality forces pointwise phase alignment with `1+e^{-idt}` almost everywhere, producing the square-wave-type extremal
\[
(\pi/2)e^{idt/2}\operatorname{sgn}(\cos(dt/2))
\]
up to symmetries. This is discontinuous at the zeros of the cosine, while actual switch traces are continuous. Formalize equality conditions in Hölder/duality carefully.

### T7 — Exact deficit identity — PROVED-HERE
If `C=||F||_infty` and `w=1+e^{-idt}`, then
\[
\frac{4C}{\pi}-2
=\frac1{2\pi}\int
(C|w|-\Re(Fw))dt.
\]

### T8 — Weighted near-equality stability — PROVED-HERE
With `C=pi/2+eps` and `E=C e^{-i arg w}` away from the zeros of `w`,
\[
\frac1{2\pi}\int |w||F-E|^2dt
\le\frac{8C}{\pi}\,\varepsilon.
\]

### T9 — Parseval third-coefficient gap — PROVED-HERE
If a switch profile has two Fourier coefficients of modulus `1` and `||F||_infty=C`, every other coefficient obeys
\[
|c_n|\le\sqrt{C^2-2}.
\]

### T10 — Binary-switch consequence — PROVED-HERE
If `C<sqrt(3)`, three simultaneous maximal coefficients are impossible because Parseval would force `C>=sqrt(3)`.

### T11 — Scaled switch-spacing lower bound — PROVED-HERE, CONDITIONAL FORM
If all sufficiently large switch norms are at most `C<sqrt(3)`, then for consecutive central vertices
\[
d_{j+1}(\tau_{j+1}-\tau_j)
\ge-\frac12\log(C^2-2).
\]
At the candidate norm this is about `0.041002712794`.

## D. Universal cocycle and Newton skeleton

### T12 — Exact renormalization cocycle — PROVED-HERE
For consecutive normalized switch profiles,
\[
F_{j+1}(z)=\xi_jz^{-d_{j+1}}F_j(q_jz),
\quad |\xi_j|=1.
\]

### T13 — Future Newton-vertex coefficient formula — PROVED-HERE
\[
|[z^{\nu_{j+m}-\nu_j}]F_j|
=\exp\left[-\sum_{\ell=j+1}^{j+m}
 d_\ell(\tau_\ell-\tau_j)\right].
\]

### T14 — Past Newton-vertex coefficient formula — PROVED-HERE
\[
|[z^{\nu_{j-m}-\nu_j}]F_j|
=\exp\left[-\sum_{\ell=j-m+1}^{j}
 d_\ell(\tau_j-\tau_\ell)\right].
\]

### T15 — Skeleton/dust decomposition — PROVED-HERE AS TERMINOLOGY
Newton vertices force the skeleton coefficients via T13–T14; all coefficients whose affine lines stay strictly below the Newton envelope are subcentral `dust`. This is a decomposition of coefficient roles, not a claim that dust is negligible.

### T16 — Gauge-invariant phase curvature — PROVED-HERE
With
\[
\eta_j=\arg(a_{\nu_j}/a_{\nu_{j-1}}),
\]
rotation `z -> e^{i theta}z` sends `eta_j -> eta_j+d_j theta`, so
\[
\Omega_j=\exp(i(d_j\eta_{j+1}-d_{j+1}\eta_j))
\]
is gauge invariant.

### T17 — Constant-jump substitution invariance — PROVED-HERE
For integer `d>=1`, `m>=0`, `c!=0`, and
\[
g(z)=z^mf(cz^d),
\]
\[
\beta(g)=\beta(f).
\]
This removes constant central-index gap as a genuine degree of freedom.

### T18 — He–Tang profile is the stationary constant-curvature cocycle — DERIVED-TARGET
Constant logarithmic switch spacing and constant phase curvature produce quadratic/triangular coefficient exponents and recover the He–Tang family up to gauge. This should be formalized as a classification statement with precise phase conventions.

## E. Finite spectral and adversarial-dual reductions

### T19 — Toeplitz compression lower bound — PROVED-HERE / STANDARD
For a continuous switch symbol `F`, its finite Toeplitz compression satisfies
\[
\|T_N(F)\|_{op}\le\|F\|_\infty.
\]

### T20 — Toeplitz norm convergence — STANDARD, FORMALIZATION TARGET
For continuous Laurent symbols,
\[
\lim_{N\to\infty}\|T_N(F)\|_{op}=\|F\|_\infty.
\]
The packet suggests a proof by an interior-shifted Fejér/Dirichlet packet plus Laurent-tail truncation.

### T21 — Adversarial `L^infty/L^1` interpolation dual — PROVED-HERE / STANDARD FUNCTIONAL ANALYSIS
For finite mandatory Fourier data `(S,b)`,
\[
\mathcal I_S(b)=
\inf_{\widehat G|_S=b}\|G\|_\infty
\]
equals
\[
\sup_{\lambda\ne0}
\frac{|\sum_{s\in S}\lambda_sb_s|}
{\frac1{2\pi}\int|\sum_{s\in S}\lambda_se^{-ist}|dt}.
\]
This gives all hidden coefficients unlimited adversarial cancellation and therefore removes the need to assume dust vanishes.

## F. Theta-family finite reductions

### T22 — Compact `K` exclusion — PROVED-HERE
Any theta-family minimizer beating the candidate lies in
\[
3/2<K<8.
\]
For `K<=3/2`, Parseval gives
\[
A^2\ge2(1+K^{-2}+K^{-6})>A_*^2.
\]
For `K>=8`, align the two leading terms and bound the rest to get
\[
A\ge2-\frac{2K^{-1}}{1-K^{-2}}>A_*.
\]

### T23 — Phase symmetry compactification — DERIVED-TARGET
`A(K,conj eps)=A(K,eps)`, so one may restrict `alpha` to a half-circle, e.g. `[0,pi]`, after choosing a consistent phase convention.

### T24 — Ramanujan triple-product representation — STANDARD + PUBLISHED THETA IDENTITY
With `q=K^{-1}`,
\[
k_{K,\varepsilon}(z)
=\Phi(qz,\varepsilon z^{-1})
=(-qz;q\varepsilon)_\infty
(-\varepsilon z^{-1};q\varepsilon)_\infty
(q\varepsilon;q\varepsilon)_\infty.
\]
He–Tang publish the `Phi` identity; the product is the classical Ramanujan/Jacobi triple product.

### T25 — Critical-point logarithmic derivative criterion — PROVED-HERE
Away from zeros of `k`, a unit-circle critical point of `|k|` satisfies
\[
\Im\left(z\frac{k'(z)}{k(z)}\right)=0.
\]

## G. First-order periodic rigidity

### T26 — Periodic first-order KKT obstruction — DERIVED-TARGET, NOT YET BANKED AS FULL THEOREM
At a stationary two-peak KKT point, translation invariance implies that for any finite-period perturbation, the sum over residue classes of the KKT-weighted first variations is zero. Hence at least one active switch/peak cannot decrease to first order. This needs a clean parameter space and differentiability proof before formal bank status.

## H. Computational reconnaissance only

### C-NUM1 — Current exact rational pair reproduces the working-report candidate — COMPUTATIONAL
Floating script returns approximately
\[
A=1.709171425067672,
\quad A^{-1}=0.585078819674513.
\]
Rigorous authority belongs to the external Arb certificate, not this script.

### C-NUM2 — Two-peak KKT system — COMPUTATIONAL
The four-variable root solve returns
\[
K=3.568185442233683,\quad
\alpha=3.961543111810228,
\]
\[
\theta=0.645541551992596,\quad
\lambda=0.289891149468333
\]
with floating residual around `1e-16`.

### C-NUM3 — Toeplitz hierarchy at the candidate — COMPUTATIONAL EVALUATION OF T19
Approximate values:

| N | `||T_N||` |
|---:|---:|
| 3 | 1.6725917242 |
| 4 | 1.6933460300 |
| 5 | 1.6990635554 |
| 10 | 1.7047619161 |
| 20 | 1.7077357508 |
| 40 | 1.7087674456 |
| 60 | 1.7089852974 |

### C-NUM4 — Small periodic curvature searches — COMPUTATIONAL
Period `2,3,4` mean-zero perturbation searches did not find a norm below the stationary candidate. This is falsification evidence only, not an optimality theorem.

### C-NUM5 — Mixed central-gap searches — COMPUTATIONAL
Tested central-only periodic patterns `(1,2)`, `(1,3)`, `(1,1,2)`, `(1,2,2)`, `(1,2,3)` were materially worse than the stationary candidate in exploratory optimization.

### C-NUM6 — Hidden odd-lane cancellation search — COMPUTATIONAL
A deliberately never-central odd coefficient lane was optimized; the optimizer pushed its amplitude toward zero. This kills one explicit bypass family, not arbitrary dust.

### C-NUM7 — Period-2 first-order flat mode and quadratic restoration — COMPUTATIONAL
A special alternating mode appeared first-order flat; along the numerically matched phase direction the objective rose approximately quadratically. This is a priority interval-certification target, not yet a theorem.

## I. Close conjectures

### C1 — Global Transition Extremality — CONJECTURE / PRIMARY CLOSE WALL
\[
\limsup_j\|F_j\|_\infty\ge A_{\rm SI}
\]
for every admissible transition cocycle arising from a transcendental entire function.

### C2 — Global Theta Minimax — CONJECTURE / FINITE CLOSE WALL
The observed two-peak KKT point globally minimizes `A(K,eps)` within the scaling-identity family.

### Consequence if C1+C2 are proved
\[
\boxed{B=A_*^{-1}\approx0.5850788196745135.}
\]
