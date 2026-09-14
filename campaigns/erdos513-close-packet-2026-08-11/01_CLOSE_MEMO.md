# Close Memo — Erdős #513

## 1. Objective

For transcendental entire
\[
f(z)=\sum_{n\ge0}a_nz^n,
\]
set
\[
M(r,f)=\max_{|z|=r}|f(z)|,\qquad
\mu(r,f)=\max_n |a_n|r^n,
\]
and
\[
\beta(f)=\liminf_{r\to\infty}\frac{\mu(r,f)}{M(r,f)},\qquad
B=\sup_f\beta(f).
\]

## 2. Exact universal reduction already available

Write `t = log r` and
\[
H(t)=\log\mu(e^t,f)=\max_n(\log|a_n|+nt),\qquad
G(t)=\log M(e^t,f).
\]
`H` is the upper envelope of affine coefficient lines; `G` is convex by Hadamard three-circles. Between consecutive breakpoints of `H`, `H-G` is concave. Therefore the defining liminf may be taken on the transition radii where the central index changes.

If `R_j=e^{\tau_j}` is such a transition and `\nu_{j-1}<\nu_j` are consecutive Newton vertices, define
\[
F_j(z)=\frac{f(R_jz)}{a_{\nu_j}R_j^{\nu_j}z^{\nu_j}}.
\]
Then
\[
\boxed{\beta(f)=\frac1{\limsup_j\|F_j\|_{L^\infty(\mathbb T)}}.}
\]

Consecutive profiles satisfy the exact cocycle
\[
F_{j+1}(z)=\xi_j z^{-d_{j+1}}F_j(q_jz),
\quad |\xi_j|=1,
\quad d_{j+1}=\nu_{j+1}-\nu_j,
\quad q_j=R_{j+1}/R_j.
\]

This is the universal object to optimize.

## 3. Candidate terminal close package

### C1 — Global Transition Extremality

Let `F_j` be the normalized transition profiles of an arbitrary transcendental entire function. Let
\[
A_{\rm SI}:=
\inf_{K>1,\,|\varepsilon|=1}
\max_{|z|=1}|k_{K,\varepsilon}(z)|,
\]
where
\[
k_{K,\varepsilon}(z)=
\sum_{n\in\mathbb Z}
\frac{\varepsilon^{n(n-1)/2}}{K^{n(n+1)/2}}z^n.
\]

**C1 asks to prove**
\[
\boxed{\limsup_{j\to\infty}\|F_j\|_\infty\ge A_{\rm SI}.}
\]

This one theorem must cover variable switch spacings, variable central-index jumps, arbitrary phase dynamics, nonperiodicity, and arbitrary subcentral coefficients.

### C2 — Global Theta Minimax

He–Tang give
\[
\beta(f_{K,\varepsilon})=
\frac1{\max_{|z|=1}|k_{K,\varepsilon}(z)|}.
\]
Using the cosine form, with `K=e^s`, `\varepsilon=e^{i\alpha}` and `T_n=n(n+1)/2`, define
\[
P_{s,\alpha}(\theta)
=2\sum_{n\ge0}e^{(-s+i\alpha)T_n}\cos((2n+1)\theta).
\]
Then
\[
A(K,e^{i\alpha})=\max_\theta |P_{s,\alpha}(\theta)|.
\]

The observed minimax point is characterized numerically by two active peak orbits and the KKT system
\[
Q(0)=Q(\theta_*),\qquad
\partial_\theta Q(\theta_*)=0,
\]
\[
\lambda\nabla_{s,\alpha}Q(0)
+(1-\lambda)\nabla_{s,\alpha}Q(\theta_*)=0,
\qquad Q=|P|^2.
\]

**C2 asks to prove** that this KKT solution is the global minimizer of `A`.

Numerical solution:
\[
K_*\approx3.568185442233683,
\quad \alpha_*\approx3.961543111810228,
\]
\[
\theta_*\approx0.645541551992596,
\quad \lambda_*\approx0.289891149468333,
\]
\[
A_*\approx1.709171425067673,
\qquad
A_*^{-1}\approx0.585078819674513.
\]

## 4. Closure chain

Published He–Tang theory gives
\[
B\ge \beta_{\rm SI}=1/A_{\rm SI}.
\]

If **C1** is proved, then every transcendental entire `f` satisfies
\[
\beta(f)\le1/A_{\rm SI},
\]
hence
\[
B=1/A_{\rm SI}.
\]

If **C2** is also proved, then `A_SI=A_*` and therefore
\[
\boxed{B=A_*^{-1}.}
\]

There is no intentionally hidden third theorem after C1+C2.

## 5. Why C1 is now sharply attackable

At each switch, the Newton vertices force exact Fourier data. All other coefficients can be treated as adversarial dust. For any finite mandatory frequency set `S` and values `b_s`, define
\[
\mathcal I_S(b)=
\inf\{\|G\|_\infty:\widehat G(s)=b_s\ (s\in S)\}.
\]
Finite-codimension `L^\infty/L^1` duality gives
\[
\mathcal I_S(b)=
\sup_{\lambda\ne0}
\frac{|\sum_{s\in S}\lambda_sb_s|}
{\frac1{2\pi}\int_0^{2\pi}|\sum_{s\in S}\lambda_se^{-ist}|dt}.
\]
Thus arbitrary hidden cancellation need not be modeled coefficient-by-coefficient.

A second finite surrogate is the Toeplitz compression
\[
T_N(F)=(\widehat F(r-s))_{0\le r,s<N},
\]
with
\[
\|T_N(F)\|_{\rm op}\le\|F\|_\infty,
\qquad
\|T_N(F)\|_{\rm op}\to\|F\|_\infty
\]
for continuous symbols. This gives a finite spectral route to C1.

## 6. Truth status

- C1: **UNPROVED**.
- C2: **UNPROVED globally**; candidate and local KKT geometry numerically reproduced.
- Exact value `B=A_*^{-1}`: **UNPROVED**.
- Explicit lower bound `B>0.585078819674`: externally reported as ball-certified for the displayed rational parameters; exact value remains open.
