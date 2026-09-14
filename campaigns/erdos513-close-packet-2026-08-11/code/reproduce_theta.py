#!/usr/bin/env python3
"""Independent floating-point reproduction for the Erdős #513 close packet.

This is NOT interval arithmetic. It is a deterministic high-precision reconnaissance
script intended to reproduce the candidate He–Tang-family parameters, the unit-circle
norm, the two active peaks, KKT residuals, and finite Toeplitz lower bounds.

For a rigorous lower-bound certificate use Arb/python-flint as in He–Tang / the July
2026 working report. This script deliberately labels every output as NONRIGOROUS.
"""
from __future__ import annotations
import math
import numpy as np
from scipy.optimize import minimize_scalar, root

K_EXACT = 713637088446737 / 200000000000000
ALPHA_EXACT = 990385777952557 / 250000000000000


def T(n: int) -> int:
    return n * (n + 1) // 2


def P(theta: float, K: float, alpha: float, nmax: int = 18) -> complex:
    # He–Tang cosine representation: e^{i theta} k(e^{i alpha} e^{2i theta})
    s = 0j
    q = complex(math.cos(alpha), math.sin(alpha)) / K
    qpow = 1 + 0j
    # Direct q**T(n) is stable here because K > 3.
    for n in range(nmax + 1):
        s += 2.0 * (q ** T(n)) * math.cos((2*n + 1) * theta)
    return s


def Q(theta: float, K: float, alpha: float, nmax: int = 18) -> float:
    v = P(theta, K, alpha, nmax)
    return (v.real*v.real + v.imag*v.imag)


def maximize_Q(K: float, alpha: float, nmax: int = 18, grid: int = 20000):
    # Symmetries allow [0, pi], but scan full period for safety.
    xs = np.linspace(0.0, 2.0*math.pi, grid, endpoint=False)
    vals = np.array([Q(float(x), K, alpha, nmax) for x in xs])
    # Refine the largest several cells to reduce grid aliasing.
    idxs = np.argpartition(vals, -12)[-12:]
    best = (-1.0, None)
    h = 2.0*math.pi/grid
    for idx in idxs:
        x0 = float(xs[idx])
        lo, hi = x0-h, x0+h
        res = minimize_scalar(lambda t: -Q(t % (2*math.pi), K, alpha, nmax),
                              bounds=(lo, hi), method='bounded',
                              options={'xatol': 1e-14, 'maxiter': 1000})
        val = -float(res.fun)
        th = float(res.x % (2*math.pi))
        if val > best[0]:
            best = (val, th)
    return math.sqrt(best[0]), best[1]


def dtheta_Q(theta, K, alpha, nmax=18):
    # analytic theta derivative of |P|^2
    p = P(theta, K, alpha, nmax)
    q = complex(math.cos(alpha), math.sin(alpha)) / K
    dp = 0j
    for n in range(nmax+1):
        dp += -2.0 * (q ** T(n)) * (2*n+1) * math.sin((2*n+1)*theta)
    return 2.0 * (p.conjugate()*dp).real


def grad_sa_Q(theta, s, alpha, nmax=18):
    K = math.exp(s)
    p = P(theta, K, alpha, nmax)
    q = complex(math.cos(alpha), math.sin(alpha)) / K
    dps = 0j
    dpa = 0j
    for n in range(nmax+1):
        tn = T(n)
        term = 2.0 * (q ** tn) * math.cos((2*n+1)*theta)
        dps += -tn * term
        dpa += 1j * tn * term
    return np.array([2.0*(p.conjugate()*dps).real,
                     2.0*(p.conjugate()*dpa).real], dtype=float)


def kkt_system(x):
    # unknowns: s, alpha, theta, lambda
    s, alpha, th, lam = x
    K = math.exp(s)
    q0 = Q(0.0, K, alpha)
    q1 = Q(th, K, alpha)
    g0 = grad_sa_Q(0.0, s, alpha)
    g1 = grad_sa_Q(th, s, alpha)
    return np.array([
        q0-q1,
        dtheta_Q(th, K, alpha),
        lam*g0[0] + (1-lam)*g1[0],
        lam*g0[1] + (1-lam)*g1[1],
    ])


def coeff(n: int, K: float, alpha: float) -> complex:
    # A_n = eps^{n(n-1)/2} / K^{n(n+1)/2}; T_n is integer also for negative n.
    phase_exp = n*(n-1)//2
    return complex(math.cos(alpha*phase_exp), math.sin(alpha*phase_exp)) * math.exp(-T(n)*math.log(K))


def toeplitz_norm(N: int, K: float, alpha: float) -> float:
    A = np.empty((N,N), dtype=np.complex128)
    for r in range(N):
        for s in range(N):
            A[r,s] = coeff(r-s, K, alpha)
    return float(np.linalg.svd(A, compute_uv=False)[0])


def compact_box_checks(Acand: float):
    smallK_lower = math.sqrt(2*(1+(1/1.5)**2+(1/1.5)**6))
    K = 8.0
    largeK_lower = 2.0 - 2.0*(K**-1)/(1-K**-2)
    return smallK_lower, largeK_lower, Acand


def main():
    print('Erdos #513 theta candidate reproduction -- NONRIGOROUS floating-point')
    print(f'K_exact_float     = {K_EXACT:.16f}')
    print(f'alpha_exact_float = {ALPHA_EXACT:.16f}')
    A, th = maximize_Q(K_EXACT, ALPHA_EXACT)
    print(f'max |P(theta)|    = {A:.15f}')
    print(f'argmax theta      = {th:.15f}')
    print(f'1/A               = {1.0/A:.15f}')
    # Locate interior active peak near the reported one and compare with theta=0.
    res_int = minimize_scalar(lambda t: -Q(t, K_EXACT, ALPHA_EXACT),
                              bounds=(0.4,0.9), method='bounded',
                              options={'xatol':1e-15})
    th_int = float(res_int.x)
    A0 = math.sqrt(Q(0.0, K_EXACT, ALPHA_EXACT))
    A1 = math.sqrt(-float(res_int.fun))
    print(f'endpoint peak      = {A0:.15f}')
    print(f'interior theta     = {th_int:.15f}')
    print(f'interior peak      = {A1:.15f}')
    print(f'peak mismatch      = {A0-A1:+.3e}')

    x0 = np.array([math.log(K_EXACT), ALPHA_EXACT, 0.645541552, 0.28989115])
    sol = root(kkt_system, x0, method='hybr', tol=1e-12)
    print(f'KKT success        = {sol.success}')
    s, a, t, lam = sol.x
    print(f'KKT K              = {math.exp(s):.15f}')
    print(f'KKT alpha          = {a:.15f}')
    print(f'KKT theta          = {t:.15f}')
    print(f'KKT lambda         = {lam:.15f}')
    print(f'KKT residual inf   = {np.max(np.abs(kkt_system(sol.x))):.3e}')
    Akkt, _ = maximize_Q(math.exp(s), a)
    print(f'KKT candidate A    = {Akkt:.15f}')
    print(f'KKT candidate 1/A  = {1.0/Akkt:.15f}')

    print('\nToeplitz compression norms (rigorous inequality, floating evaluation):')
    prev = 0.0
    for N in [3,4,5,10,20,40,60]:
        tn = toeplitz_norm(N, K_EXACT, ALPHA_EXACT)
        print(f'N={N:2d}  ||T_N||={tn:.10f}  monotone_step={tn-prev:+.3e}')
        prev = tn

    sm, lg, ac = compact_box_checks(A)
    print('\nCompact-box exclusion checks:')
    print(f'K<=1.5 Parseval lower at boundary = {sm:.12f} > A? {sm > ac}')
    print(f'K>=8 alignment lower at boundary = {lg:.12f} > A? {lg > ac}')

    rho = math.sqrt(A*A - 2.0)
    sep = -0.5*math.log(A*A-2.0)
    print('\nNear-record switch consequences:')
    print(f'rho=sqrt(A^2-2) = {rho:.12f}')
    print(f'd*s >= -0.5 log(A^2-2) = {sep:.12f}')

if __name__ == '__main__':
    main()
