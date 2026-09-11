"""
P1 ADMISSIBILITY FILTER  (campaign R008, COURT_PROVED -- NOT kernel-checked).

Statement (Kuerschak 1918 generalised to every prime; the campaign's P1):
  Let S be a finite set of integers >= 2 with sum_{n in S} 1/n IN Z.  Fix a prime p
  with p^2 > B >= max(S), and put A = { n/p : n in S, p | n } subset {1..m},
  m = floor(B/p) < p.  Then either A is empty or
        v_p( sum_{j in A} 1/j ) >= 1,
  i.e. p divides the numerator of sum_{j in A} 1/j in lowest terms.

Proof sketch (elementary, reproduced so the filter is auditable):
  p^2 > B forces v_p(n) = 1 for every n in S divisible by p, so
  sum_{n in S} 1/n = T + (1/p) * sum_{j in A} 1/j  with v_p(T) >= 0.
  Every j <= m < p, so the denominator of sum_{j in A} 1/j is prime to p and
  v_p of the second term is v_p(numerator) - 1.  If that is negative the total
  has v_p < 0 and cannot be the integer 1.

Consequence used as a search prune: an integer n = j*p in [2,B] is BANNED from S
whenever no nonempty A subset {1..m} containing j satisfies p | numerator.
The classical corollaries fall out: every prime in (B/2, B] is banned (m = 1,
numerator 1), and for p in (B/3, B/2] both p and 2p are banned (numerators
1, 1, 3).

This filter is COURT_PROVED in the campaign, not kernel-checked.  Every receipt
produced with it carries prune_tier = "COURT_PROVED(P1)"; the primary receipts
are produced WITHOUT it, using only KERNEL_CHECKED facts.
Integer arithmetic only.
"""


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if s[i]:
            s[i * i:: i] = bytearray(len(s[i * i:: i]))
        i += 1
    return [i for i in range(2, n + 1) if s[i]]


def banned_set(B, mmax=13):
    """Return (banned_bool_list, report_dict).  banned[n] True => n cannot lie in S."""
    banned = [False] * (B + 2)
    detail = []
    for p in primes_upto(B):
        if p * p <= B:
            continue
        m = B // p
        if m == 0 or m > mmax:
            continue
        # L = lcm(1..m); p > m so p does not divide L.
        L = 1
        for i in range(1, m + 1):
            g = L
            b = i
            while b:
                g, b = b, g % b
            L = L * i // g
        wj = [0] + [L // i for i in range(1, m + 1)]
        # subset sums over {1..m} by DP on masks
        keep = [False] * (m + 1)
        sums = [0] * (1 << m)
        for mask in range(1, 1 << m):
            low = mask & (-mask)
            i = low.bit_length()  # 1-based index
            sums[mask] = sums[mask ^ low] + wj[i]
            if sums[mask] % p == 0:
                mm = mask
                while mm:
                    lo = mm & (-mm)
                    keep[lo.bit_length()] = True
                    mm ^= lo
        nb = 0
        for j in range(1, m + 1):
            if not keep[j]:
                banned[j * p] = True
                nb += 1
        if nb:
            detail.append({"p": p, "m": m, "banned_multipliers": [j for j in range(1, m + 1) if not keep[j]]})
    n_banned = sum(1 for n in range(2, B + 1) if banned[n])
    return banned, {"B": B, "mmax": mmax, "n_banned": n_banned, "primes_with_bans": len(detail)}


if __name__ == "__main__":
    import sys
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    b, rep = banned_set(B)
    print(rep)
    print("banned:", [n for n in range(2, B + 1) if b[n]][:80], "...")
