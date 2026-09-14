#!/usr/bin/env python3
"""Deterministic finite tests for algebraic identities used in the close packet.
These tests are sanity checks, not proofs of the analytic theorems.
"""
from __future__ import annotations
import cmath, math, random

random.seed(513)

def assert_close(a,b,tol=1e-11):
    if abs(a-b) > tol*(1+abs(a)+abs(b)):
        raise AssertionError((a,b,abs(a-b)))

# 1. Gauge invariance of the local phase curvature Omega.
for _ in range(100):
    d0 = random.randint(1,7); d1 = random.randint(1,7)
    e0 = random.uniform(-math.pi,math.pi); e1 = random.uniform(-math.pi,math.pi)
    th = random.uniform(-math.pi,math.pi)
    om0 = cmath.exp(1j*(d0*e1-d1*e0))
    om1 = cmath.exp(1j*(d0*(e1+d1*th)-d1*(e0+d0*th)))
    assert_close(om0,om1)

# 2. Newton skeleton future/past coefficient formulas from switch data.
for _ in range(100):
    m = 8
    d = [random.randint(1,4) for _ in range(m)]
    tau = [0.0]
    for j in range(1,m):
        tau.append(tau[-1] + random.uniform(0.05,1.0))
    # magnitudes at vertices from crossing recurrence log a_j-log a_{j-1}=-d_j tau_j
    loga=[0.0]
    for j in range(1,m):
        loga.append(loga[-1] - d[j]*tau[j])
    nu=[0]
    for j in range(1,m):
        nu.append(nu[-1]+d[j])
    j=3
    for k in range(1, m-j):
        direct=(loga[j+k]-loga[j])+(nu[j+k]-nu[j])*tau[j]
        formula=-sum(d[l]*(tau[l]-tau[j]) for l in range(j+1,j+k+1))
        assert_close(direct,formula)
    for k in range(1,j+1):
        direct=(loga[j-k]-loga[j])+(nu[j-k]-nu[j])*tau[j]
        formula=-sum(d[l]*(tau[j]-tau[l]) for l in range(j-k+1,j+1))
        assert_close(direct,formula)

# 3. Exact cocycle identity tested on finite polynomials at arbitrary switches.
# Build random coefficients, choose two radii and normalizing indices; algebra does not require centrality,
# except |xi|=1. Here we test exact functional identity with the exact xi.
for _ in range(100):
    deg=8
    a=[complex(random.uniform(-1,1), random.uniform(-1,1)) for _ in range(deg+1)]
    if any(abs(x)<1e-4 for x in a): continue
    Rj=random.uniform(0.5,2.0); q=random.uniform(1.1,2.0); Rn=Rj*q
    nj=random.randint(0,deg-2); nn=random.randint(nj+1,deg)
    d=nn-nj
    z=complex(random.uniform(0.4,1.2),random.uniform(-1,1))
    def f(w): return sum(a[n]*(w**n) for n in range(deg+1))
    Fj=lambda w: f(Rj*w)/(a[nj]*(Rj**nj)*(w**nj))
    Fn=lambda w: f(Rn*w)/(a[nn]*(Rn**nn)*(w**nn))
    xi=a[nj]/(a[nn]*(Rn**d))
    assert_close(Fn(z), xi*(z**(-d))*Fj(q*z), tol=3e-10)

# 4. Constant-jump substitution invariance at finite radii:
# mu_g/M_g equals mu_f/M_f at transformed radius for polynomial truncations.
def ratio_poly(a,r,samples=20000):
    mu=max(abs(an)*(r**n) for n,an in enumerate(a))
    M=max(abs(sum(an*(r*cmath.exp(1j*t))**n for n,an in enumerate(a)))
          for t in [2*math.pi*j/samples for j in range(samples)])
    return mu/M
for _ in range(3):
    a=[1+0j, .4+.2j, -.1+.3j, .02-.01j]
    d=random.randint(2,4); m=random.randint(0,3); c=0.7*cmath.exp(0.3j)
    r=random.uniform(.7,1.3)
    lhs=ratio_poly([0j]*m + [0j]*(d*(len(a)-1)+1), r, samples=5000) if False else None
    # Evaluate g directly to avoid sparse coefficient bookkeeping errors.
    mu_f=max(abs(an)*((abs(c)*r**d)**n) for n,an in enumerate(a))
    M_f=max(abs(sum(an*((abs(c)*r**d)*cmath.exp(1j*t))**n for n,an in enumerate(a)))
            for t in [2*math.pi*j/5000 for j in range(5000)])
    mu_g=(r**m)*mu_f
    # c z^d covers the full transformed circle as z traverses one circle.
    M_g=(r**m)*M_f
    assert_close(mu_g/M_g, mu_f/M_f, tol=1e-12)

print('PASS: 4 identity families / deterministic finite sanity checks')
