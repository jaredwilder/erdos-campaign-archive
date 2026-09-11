"""
Erdos 289 -- k-block interval-decomposition search, SHARDED BY FIRST-RUN START.

EXACT ARITHMETIC ONLY.  There is no float anywhere in this file.
The whole search runs in the integer ring after clearing denominators by
M = lcm(2..B):  a set S of integers with sum_{n in S} 1/n = 1  is exactly a set
with sum_{n in S} (M/n) = M.  Every bound, every prune, every comparison is an
exact big-integer comparison.

DOMAIN (derived from the frozen contract, see report for verbatim quotes):
  a block is an interval I=[a,b] of consecutive integers, a >= 2, b >= a+1
  (so |I| >= 2); blocks sorted by start are pairwise non-overlapping AND
  non-adjacent: next.a >= prev.b + 2; the target is EXACT equality
  sum_i sum_{n in I_i} 1/n = 1 in Q.

KERNEL PRUNES USED (campaign kernel/Erdos289Head.lean, all VERIFIED, axioms
{propext, Classical.choice, Quot.sound}):
  F1_head_forced : (1/2 + 1/3 + 1/4 > 1)
      => the block containing 2 must be exactly [2,3].  (A block containing 2
         must start at 2 since starts are >= 2; it cannot be [2,2] since
         |I| >= 2; and [2,4] already exceeds 1.)
  F1_tail_value  : 1 - (1/2 + 1/3) = 1/6
      => when the head [2,3] is taken, the remaining k-1 blocks must sum to
         exactly 1/6, and non-adjacency forces every later start >= 5.
  W4_fragment    : no run [a,b] with 5 <= a < b <= 60 has reciprocal sum 1/6
      => with F1, the shard a1=2 admits no completion at k=2, and at the LAST
         block of any run the pair (rem = 1/6, s >= 5, b <= 60) is dead.

CLI:
  python search289.py --k K --B B --shard A1 [--budget NODES] [--out FILE]
  python search289.py --k K --B B --allshards [--budget NODES] [--out FILE]
"""
import argparse
import json
import os
import sys
import time
from bisect import bisect_left
from math import gcd

BUDGET_SENTINEL = "BUDGET_STOPPED"


class Budget(Exception):
    def __init__(self, where):
        self.where = where


class Board:
    """Precomputed exact integer tables for a fixed bound B."""

    def __init__(self, B, p1ban=False):
        self.B = B
        self.p1ban = p1ban
        M = 1
        for n in range(2, B + 1):
            M = M * n // gcd(M, n)
        self.M = M
        # w[n] = M/n  (exact integer)
        w = [0] * (B + 2)
        for n in range(2, B + 1):
            w[n] = M // n
        self.w = w
        # Pre[n] = sum_{i=2..n} w[i]; Pre[0]=Pre[1]=0
        Pre = [0] * (B + 2)
        acc = 0
        for n in range(2, B + 1):
            acc += w[n]
            Pre[n] = acc
        Pre[B + 1] = acc
        self.Pre = Pre
        # L[s] = lcm(s..B), Gs[s] = M // L[s].
        # Any sum of reciprocals of a subset of [s,B] has denominator dividing
        # L[s]; cleared by M this means the integer value is divisible by Gs[s].
        L = [1] * (B + 3)
        cur = 1
        for s in range(B, 1, -1):
            cur = cur * s // gcd(cur, s)
            L[s] = cur
        self.Gs = [1] * (B + 3)
        for s in range(2, B + 2):
            self.Gs[s] = M // L[s] if L[s] else 1
        # UBloss[j] : a LOWER bound on the total weight that MUST be omitted
        # inside [s,B] when exactly j blocks live there.  The i-th of the j-1
        # internal gaps sits at a position <= B-2-3t (t = 0..j-2) counting from
        # the right, so the omitted weight is >= sum_t w[B-2-3t].
        # LBmin[j] : the minimum achievable weight of j blocks inside [s,B],
        # realised by j length-2 blocks pushed as far right as possible.
        self.UBloss = [0] * (B + 3)
        self.LBmin = [0] * (B + 3)
        acc = 0
        j = 1
        self.UBloss[1] = 0
        while True:
            t = j - 1  # gap index for block count j+1
            pos = B - 2 - 3 * (t)
            if pos < 2 or j + 1 > B:
                break
            acc += w[pos]
            self.UBloss[j + 1] = acc
            j += 1
        self.maxblocks_ub = j
        acc = 0
        j = 0
        while True:
            hi = B - 3 * j
            lo = hi - 1
            if lo < 2:
                break
            acc += w[hi] + w[lo]
            j += 1
            self.LBmin[j] = acc
        self.maxblocks_lb = j
        # for j beyond the tables the configuration is infeasible anyway
        for jj in range(self.maxblocks_ub + 1, B + 3):
            self.UBloss[jj] = self.UBloss[self.maxblocks_ub]
        for jj in range(self.maxblocks_lb + 1, B + 3):
            self.LBmin[jj] = None  # infeasible marker
        # P1 admissibility filter (court-proved, OPTIONAL, off by default)
        if p1ban:
            from p1ban import banned_set
            ban, rep = banned_set(B)
            self.ban = ban
            self.ban_report = rep
        else:
            self.ban = [False] * (B + 2)
            self.ban_report = {"B": B, "n_banned": 0, "enabled": False}
        # nextban[a] = least banned index >= a  (B+1 if none)
        nb = [B + 1] * (B + 3)
        nxt = B + 1
        for n in range(B, 1, -1):
            if self.ban[n]:
                nxt = n
            nb[n] = nxt
        self.nextban = nb

    def ub(self, s, j):
        """Exact upper bound on the total weight of j legal blocks inside [s,B]."""
        return self.Pre[self.B] - self.Pre[s - 1] - self.UBloss[j]

    def lb(self, j):
        return self.LBmin[j]


def search_shard(board, k, a1, budget, tnum=1, tden=1):
    """DFS.  Returns (outcome, payload, nodes).

    outcome in {'WITNESS','EXHAUSTED','BUDGET_STOPPED'}
    tnum/tden: the exact rational target (default 1).  Non-unit targets exist
    only to run known-answer controls against the naive enumerator; the
    kernel head prune is switched off whenever the target is not exactly 1.
    """
    B = board.B
    w = board.w
    Pre = board.Pre
    Gs = board.Gs
    UBloss = board.UBloss
    LBmin = board.LBmin
    if board.M % tden:
        raise SystemExit("target denominator %d does not divide lcm(2..%d)" % (tden, B))
    M = board.M // tden * tnum
    head_prune = (tnum == 1 and tden == 1)
    ban = board.ban
    nextban = board.nextban
    nodes = 0
    blocks = []

    def dfs(s, rem, j):
        nonlocal nodes
        nodes += 1
        if nodes > budget:
            raise Budget(list(blocks) + [("at_start", s, "blocks_left", j)])
        if rem <= 0:
            return False
        if B - s + 1 < 3 * j - 1:
            return False
        lbj = LBmin[j] if j < len(LBmin) else None
        if lbj is None or rem < lbj:
            return False
        if rem > Pre[B] - Pre[s - 1] - UBloss[j]:
            return False
        g = Gs[s]
        if g > 1 and rem % g:
            return False
        # --- last block: solve by exact binary search on the prefix table ---
        if j == 1:
            a = s
            while a <= B - 1:
                if Pre[B] - Pre[a - 1] < rem:
                    break
                if ban[a] or ban[a + 1]:
                    a += 1
                    continue
                target = rem + Pre[a - 1]
                idx = bisect_left(Pre, target, a + 1, B + 1)
                if idx <= B and idx < nextban[a] and Pre[idx] == target:
                    blocks.append((a, idx))
                    return True
                a += 1
            return False
        # --- interior block ---
        room = 3 * (j - 1) - 1  # room the remaining j-1 blocks need after b+2
        lbnext = LBmin[j - 1]
        a = s
        amax = B - (3 * j - 1) + 1
        while a <= amax:
            if Pre[B] - Pre[a - 1] - UBloss[j] < rem:
                break
            if a == 2 and head_prune:
                # KERNEL F1_head_forced: the block containing 2 is exactly [2,3].
                cur = w[2] + w[3]
                if cur <= rem - lbnext:
                    nrem = rem - cur
                    blocks.append((2, 3))
                    if dfs(5, nrem, j - 1):
                        return True
                    blocks.pop()
                a += 1
                continue
            if ban[a]:
                a += 1
                continue
            cur = w[a]
            b = a + 1
            cap = rem - lbnext
            while b <= B:
                if ban[b]:
                    break
                cur += w[b]
                if cur > cap:
                    break
                if B - (b + 2) + 1 >= room:
                    nrem = rem - cur
                    blocks.append((a, b))
                    if dfs(b + 2, nrem, j - 1):
                        return True
                    blocks.pop()
                b += 1
            a += 1
        return False

    # top level is unrolled on the shard value a1
    try:
        if a1 == 2 and head_prune:
            # KERNEL F1_head_forced + F1_tail_value
            cur = w[2] + w[3]
            rem = M - cur
            blocks.append((2, 3))
            if k == 1:
                ok = False
            else:
                lbnext = LBmin[k - 1] if (k - 1) < len(LBmin) else None
                ok = (lbnext is not None) and rem > 0 and dfs(5, rem, k - 1)
            if ok:
                return ("WITNESS", list(blocks), nodes)
            return ("EXHAUSTED", None, nodes)
        a = a1
        if a > B - (3 * k - 1) + 1:
            return ("EXHAUSTED", None, nodes)
        if Pre[B] - Pre[a - 1] - UBloss[k] < M:
            return ("EXHAUSTED", None, nodes)
        if ban[a]:
            return ("EXHAUSTED", None, nodes)
        cur = w[a]
        lbnext = LBmin[k - 1] if k >= 2 and (k - 1) < len(LBmin) else 0
        if k >= 2 and lbnext is None:
            return ("EXHAUSTED", None, nodes)
        cap = M - (lbnext if k >= 2 else 0)
        room = 3 * (k - 1) - 1
        b = a + 1
        while b <= B:
            if ban[b]:
                break
            cur += w[b]
            if cur > cap:
                break
            if k == 1:
                if cur == M:
                    return ("WITNESS", [(a, b)], nodes)
            else:
                if B - (b + 2) + 1 >= room:
                    blocks.append((a, b))
                    if dfs(b + 2, M - cur, k - 1):
                        return ("WITNESS", list(blocks), nodes)
                    blocks.pop()
            b += 1
        return ("EXHAUSTED", None, nodes)
    except Budget as e:
        return ("BUDGET_STOPPED", e.where, nodes)


def shard_range(board, k, tnum=1, tden=1):
    """The exact set of first-run starts that can possibly begin a k-decomposition."""
    B = board.B
    M = board.M // tden * tnum
    out = []
    for a in range(2, B - (3 * k - 1) + 2):
        if board.ban[a] or board.ban[a + 1]:
            continue
        if board.Pre[B] - board.Pre[a - 1] - board.UBloss[k] >= M:
            out.append(a)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--B", type=int, required=True)
    ap.add_argument("--shard", type=int, default=None)
    ap.add_argument("--allshards", action="store_true")
    ap.add_argument("--budget", type=int, default=20_000_000)
    ap.add_argument("--wall", type=float, default=0.0, help="soft wall-clock cap (s) for --allshards")
    ap.add_argument("--out", default=None)
    ap.add_argument("--tnum", type=int, default=1)
    ap.add_argument("--tden", type=int, default=1)
    ap.add_argument("--p1ban", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    board = Board(args.B, p1ban=args.p1ban)
    tprep = time.time() - t0
    shards = shard_range(board, args.k, args.tnum, args.tden)
    rec = {
        "problem": "erdos289",
        "k": args.k,
        "B": args.B,
        "target": "%d/%d" % (args.tnum, args.tden),
        "M_bits": board.M.bit_length(),
        "prep_seconds": round(tprep, 3),
        "shard_axis": "first-run start a1",
        "shard_domain": [shards[0], shards[-1]] if shards else [],
        "n_shards": len(shards),
        "budget_nodes_per_shard": args.budget,
        "shards": [],
    }
    todo = shards if args.allshards else ([args.shard] if args.shard is not None else shards)
    witness = None
    for a1 in todo:
        ts = time.time()
        outcome, payload, nodes = search_shard(
            board, args.k, a1, args.budget, args.tnum, args.tden
        )
        row = {
            "shard": a1,
            "k": args.k,
            "bound_B": args.B,
            "nodes": nodes,
            "seconds": round(time.time() - ts, 3),
            "outcome": outcome,
        }
        if outcome == "WITNESS":
            row["blocks"] = [[int(x), int(y)] for x, y in payload]
            witness = row["blocks"]
        elif outcome == "BUDGET_STOPPED":
            row["stopped_at"] = str(payload)
        rec["shards"].append(row)
        print(
            "k=%d B=%d shard a1=%d -> %s nodes=%d %.2fs"
            % (args.k, args.B, a1, outcome, nodes, row["seconds"]),
            flush=True,
        )
        if outcome == "WITNESS":
            break
        if args.wall and (time.time() - t0) > args.wall:
            rec["wall_cap_hit_after_shard"] = a1
            print("WALL CAP HIT after shard %d" % a1, flush=True)
            break
    done = [r for r in rec["shards"] if r["outcome"] == "EXHAUSTED"]
    rec["total_seconds"] = round(time.time() - t0, 3)
    rec["total_nodes"] = sum(r["nodes"] for r in rec["shards"])
    if witness:
        rec["verdict"] = "WITNESS"
        rec["witness"] = witness
    elif len(done) == len(shards):
        rec["verdict"] = "EXHAUSTED"
        rec["verdict_statement"] = (
            "No decomposition of 1 into exactly %d non-adjacent blocks of consecutive "
            "integers, each of length >= 2, with every element in [2,%d]. "
            "This is COMPUTATION evidence bounded by B=%d; it is NOT a closure."
            % (args.k, args.B, args.B)
        )
    else:
        rec["verdict"] = "PARTIAL"
        rec["verdict_statement"] = (
            "Shards exhausted: %d of %d at k=%d, bound B=%d. Remaining shards "
            "budget-stopped or unrun. NOT an exhaustion claim."
            % (len(done), len(shards), args.k, args.B)
        )
    out = args.out or ("k%d_B%d.json" % (args.k, args.B))
    with open(out, "w", encoding="utf-8", errors="replace") as f:
        json.dump(rec, f, indent=1)
    print("VERDICT %s -> %s" % (rec["verdict"], out), flush=True)


if __name__ == "__main__":
    main()
