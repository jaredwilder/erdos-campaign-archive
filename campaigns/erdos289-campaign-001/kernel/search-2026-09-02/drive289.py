"""
Erdos 289 sharded siege driver.  Runs search289 shards across all cores.

python drive289.py --jobs "3:400,4:260" --workers 20 --budget 20000000 \
                   --deadline 3600 --tag r1 --outdir <campaign kernel search dir>

Every shard produces its own receipt row.  A shard that hits its node budget is
recorded as BUDGET_STOPPED with the point it stopped -- never as EXHAUSTED.
"""
import argparse
import json
import os
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from search289 import Board, search_shard, shard_range  # noqa: E402

_BOARDS = {}


def get_board(B, p1ban):
    key = (B, p1ban)
    if key not in _BOARDS:
        _BOARDS.clear()
        _BOARDS[key] = Board(B, p1ban=p1ban)
    return _BOARDS[key]


def work(job):
    k, B, a1, budget, p1ban = job
    board = get_board(B, p1ban)
    t0 = time.time()
    outcome, payload, nodes = search_shard(board, k, a1, budget)
    row = {
        "shard": a1,
        "k": k,
        "bound_B": B,
        "nodes": nodes,
        "node_budget": budget,
        "seconds": round(time.time() - t0, 3),
        "outcome": outcome,
        "prune_tier": "COURT_PROVED(P1)+KERNEL" if p1ban else "KERNEL_ONLY",
    }
    if outcome == "WITNESS":
        row["blocks"] = [[int(x), int(y)] for x, y in payload]
    elif outcome == "BUDGET_STOPPED":
        row["stopped_at"] = str(payload)
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", required=True, help="comma list of k:B")
    ap.add_argument("--workers", type=int, default=20)
    ap.add_argument("--budget", type=int, default=20_000_000)
    ap.add_argument("--deadline", type=float, default=3600.0)
    ap.add_argument("--tag", default="r")
    ap.add_argument("--question-lock", default=None)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--p1ban", action="store_true")
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)
    jobs = []
    for tok in args.jobs.split(","):
        k, B = tok.split(":")
        jobs.append((int(k), int(B)))
    t_start = time.time()
    all_rows = []
    summary = []
    for (k, B) in jobs:
        if time.time() - t_start > args.deadline:
            summary.append({"k": k, "bound_B": B, "verdict": "NOT_RUN_DEADLINE"})
            print("SKIP k=%d B=%d (global deadline)" % (k, B), flush=True)
            continue
        board = Board(B, p1ban=args.p1ban)
        shards = shard_range(board, k)
        nban = board.ban_report
        del board
        if not shards:
            summary.append(
                {
                    "k": k,
                    "bound_B": B,
                    "verdict": "EMPTY_DOMAIN",
                    "note": "no first-run start admits enough weight for %d blocks in [2,%d]" % (k, B),
                }
            )
            print("k=%d B=%d EMPTY_DOMAIN" % (k, B), flush=True)
            continue
        tasks = [(k, B, a1, args.budget, args.p1ban) for a1 in shards]
        t0 = time.time()
        rows = []
        witness = None
        with Pool(processes=args.workers) as pool:
            for row in pool.imap_unordered(work, tasks, chunksize=1):
                rows.append(row)
                if row["outcome"] == "WITNESS":
                    witness = row
                    print("*** WITNESS k=%d B=%d shard=%d %s" % (k, B, row["shard"], row["blocks"]), flush=True)
                    pool.terminate()
                    break
        rows.sort(key=lambda r: r["shard"])
        nex = sum(1 for r in rows if r["outcome"] == "EXHAUSTED")
        nbud = sum(1 for r in rows if r["outcome"] == "BUDGET_STOPPED")
        el = time.time() - t0
        if witness:
            verdict = "WITNESS"
        elif nex == len(shards):
            verdict = "EXHAUSTED"
        else:
            verdict = "PARTIAL"
        item = {
            "k": k,
            "bound_B": B,
            "n_shards": len(shards),
            "shard_domain": [shards[0], shards[-1]],
            "shards_exhausted": nex,
            "shards_budget_stopped": nbud,
            "shards_run": len(rows),
            "total_nodes": sum(r["nodes"] for r in rows),
            "wall_seconds": round(el, 2),
            "verdict": verdict,
            "prune_tier": "COURT_PROVED(P1)+KERNEL" if args.p1ban else "KERNEL_ONLY",
            "p1_ban_report": nban,
        }
        if witness:
            item["witness_blocks"] = witness["blocks"]
        item["statement"] = (
            "k=%d, every element in [2,%d], shard axis = first-run start a1 in [%d,%d]: %s"
            % (k, B, shards[0], shards[-1], verdict)
        )
        summary.append(item)
        all_rows.extend(rows)
        fn = os.path.join(args.outdir, "shards-k%02d-B%04d-%s.json" % (k, B, args.tag))
        with open(fn, "w", encoding="utf-8", errors="replace") as f:
            json.dump({"job": item, "shards": rows}, f, indent=1)
        print(
            "k=%2d B=%4d shards=%4d exhausted=%4d budget=%3d nodes=%12d %.1fs -> %s"
            % (k, B, len(shards), nex, nbud, item["total_nodes"], el, verdict),
            flush=True,
        )
        if witness:
            break
    out = os.path.join(args.outdir, "round-%s.json" % args.tag)
    with open(out, "w", encoding="utf-8", errors="replace") as f:
        json.dump(
            {
                "tag": args.tag,
                "workers": args.workers,
                "node_budget_per_shard": args.budget,
                "p1ban": args.p1ban,
                "global_deadline_seconds": args.deadline,
                "wall_seconds": round(time.time() - t_start, 2),
                "jobs": summary,
            },
            f,
            indent=1,
        )
    print("ROUND DONE -> %s" % out, flush=True)


if __name__ == "__main__":
    main()
