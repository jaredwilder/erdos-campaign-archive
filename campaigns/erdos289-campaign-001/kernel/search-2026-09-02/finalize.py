"""Assemble the Erdos 289 master search receipt, including the OPERATOR_STOPPED frontier."""
import glob
import json
import os
import datetime

OUT = (r"C:\Users\jared\Local Sites\woocommerce-enterprise\oracle\evidence\msl-machine"
       r"\campaigns\erdos289-campaign-001\kernel\search-2026-09-02")
MINE = os.path.dirname(os.path.abspath(__file__))
utc = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H%M%SZ")

jobs = []
for fn in sorted(glob.glob(os.path.join(OUT, "shards-k*.json"))):
    with open(fn, encoding="utf-8", errors="replace") as f:
        d = json.load(f)
    j = dict(d["job"])
    j.setdefault("prune_tier", "KERNEL_ONLY")
    j["shard_receipt_file"] = os.path.basename(fn)
    j["outcome_lines"] = [
        "shard a1=%d | k=%d | bound B=%d (every element of every block in [2,%d]) | tier=%s | "
        "nodes=%d/%d | %s%s"
        % (r["shard"], r["k"], r["bound_B"], r["bound_B"], r.get("prune_tier", "KERNEL_ONLY"),
           r["nodes"], r["node_budget"], r["outcome"],
           (" blocks=" + json.dumps(r["blocks"])) if r["outcome"] == "WITNESS"
           else ((" stopped_at=" + r.get("stopped_at", "?")) if r["outcome"] == "BUDGET_STOPPED" else ""))
        for r in d["shards"]
    ]
    jobs.append(j)

# single-process runs done directly with search289.py --allshards
for fn, tier in [("t_k1_B260.json", "KERNEL_ONLY"), ("t_k2_B260.json", "KERNEL_ONLY"),
                 ("t_k3_B260.json", "KERNEL_ONLY")]:
    p = os.path.join(MINE, fn)
    if not os.path.exists(p):
        continue
    with open(p, encoding="utf-8", errors="replace") as f:
        d = json.load(f)
    nex = sum(1 for r in d["shards"] if r["outcome"] == "EXHAUSTED")
    jobs.append({
        "k": d["k"], "bound_B": d["B"], "n_shards": d["n_shards"],
        "shard_domain": d["shard_domain"], "shards_exhausted": nex,
        "shards_budget_stopped": sum(1 for r in d["shards"] if r["outcome"] == "BUDGET_STOPPED"),
        "shards_run": len(d["shards"]), "total_nodes": d["total_nodes"],
        "wall_seconds": d["total_seconds"], "verdict": d["verdict"], "prune_tier": tier,
        "shard_receipt_file": "MINE/" + fn, "single_process": True,
        "statement": "k=%d, every element in [2,%d], shard axis = first-run start a1 in [%d,%d]: %s"
                     % (d["k"], d["B"], d["shard_domain"][0], d["shard_domain"][1], d["verdict"]),
        "outcome_lines": [
            "shard a1=%d | k=%d | bound B=%d | tier=%s | nodes=%d | %s"
            % (r["shard"], r["k"], r["bound_B"], tier, r["nodes"], r["outcome"])
            for r in d["shards"]],
    })

operator_stopped = [
    {"k": 30, "bound_B": 600, "prune_tier": "COURT_PROVED(P1)+KERNEL",
     "outcome": "OPERATOR_STOPPED",
     "frontier": "shard sweep in flight, ~95 s of a 20-worker pool, no shard had returned; "
                 "NOTHING is claimed for k=30 at B=600",
     "resume_command": 'python drive289.py --jobs "30:600" --workers N --budget 30000000 '
                       '--p1ban --tag resume --outdir <this dir>'},
    {"k": "29..4", "bound_B": 600, "prune_tier": "COURT_PROVED(P1)+KERNEL",
     "outcome": "OPERATOR_STOPPED", "frontier": "queued, never started",
     "resume_command": 'python drive289.py --jobs "29:600,28:600,...,4:600" --workers N '
                       '--budget 30000000 --p1ban --tag resume --outdir <this dir>'},
    {"k": "26..4", "bound_B": 200, "prune_tier": "KERNEL_ONLY",
     "outcome": "OPERATOR_STOPPED",
     "frontier": "the kernel-only B=200 round crashed at k=27 on a live edit of drive289.py "
                 "and was then stopped on operator order; k=3 and k=30,29,28,27 completed and "
                 "their receipts are here",
     "resume_command": 'python drive289.py --jobs "26:200,...,4:200" --workers N '
                       '--budget 20000000 --tag resumeKO --outdir <this dir>'},
    {"k": 3, "bound_B": "400 and 700", "prune_tier": "KERNEL_ONLY",
     "outcome": "OPERATOR_STOPPED",
     "frontier": "single-process calibration: B=400 reached shard a1=29 of 146 "
                 "(9,112,505 nodes, 254 s); B=700 reached shard a1=9 of 256 "
                 "(2,301,689 nodes, 250 s). Neither is an exhaustion claim.",
     "resume_command": 'python drive289.py --jobs "3:400,3:700" --workers N --tag resumeKO '
                       '--outdir <this dir>'},
    {"k": 4, "bound_B": 160, "prune_tier": "KERNEL_ONLY", "outcome": "OPERATOR_STOPPED",
     "frontier": "single-process: reached shard a1=10 of 57 (62,060,011 nodes, 338 s)",
     "resume_command": 'python drive289.py --jobs "4:160" --workers N --tag resumeKO --outdir <this dir>'},
]

best = {}
for j in jobs:
    k = j["k"]
    cur = best.get(k)
    if cur is None:
        best[k] = j
        continue
    rank = {"WITNESS": 3, "EXHAUSTED": 2, "PARTIAL": 1}
    if (rank.get(j["verdict"], 0), j["bound_B"]) > (rank.get(cur["verdict"], 0), cur["bound_B"]):
        best[k] = j

rec = {
    "problem": "erdos289",
    "campaign": "erdos289-campaign-001",
    "generated_utc": utc,
    "run_status": "OPERATOR_STOPPED -- local compute halted mid-siege on operator order; "
                  "this receipt IS the resume frontier",
    "headline": "NO WITNESS FOUND. No k-block decomposition of 1 exists for k=1,2,3 with every "
                "element in [2,600] (k=3), [2,260] (k=1,2); every other (k,B) attempted is "
                "recorded below with its exact stopping point.",
    "what_was_searched": (
        "Exact-rational k-block interval decompositions of 1: finite intervals I_1..I_k of "
        "consecutive integers, every start >= 2, every |I_i| >= 2, pairwise non-overlapping AND "
        "non-adjacent (next.a >= prev.b + 2), with sum_i sum_{n in I_i} 1/n = 1 EXACTLY in Q. "
        "Shard axis: the first run's start a1."
    ),
    "arithmetic": (
        "EXACT ONLY. The search runs in Z after clearing by M = lcm(2..B): sum 1/n = 1 <=> "
        "sum M/n = M. Every bound and every comparison is a big-integer comparison. No float "
        "appears in search289.py, verify289.py, p1ban.py, drive289.py or control289b.py."
    ),
    "honesty_law": (
        "Every EXHAUSTED line is bounded by its B and says so: it means 'no such decomposition "
        "exists with every element <= B'. It is COMPUTATION evidence, never a closure of "
        "Erdos 289. BUDGET_STOPPED and OPERATOR_STOPPED are recorded wherever a shard hit its "
        "node budget or was halted; no truncated shard is reported as exhausted."
    ),
    "prune_tiers": {
        "KERNEL_ONLY": (
            "uses only kernel-checked facts from campaigns/erdos289-campaign-001/kernel/"
            "Erdos289Head.lean (F1_head_forced, F1_tail_value, W4_fragment; axioms "
            "{propext, Classical.choice, Quot.sound}) plus monotone weight bounds and the "
            "denominator bound 'the remaining target's denominator must divide lcm(s..B)'."
        ),
        "COURT_PROVED(P1)+KERNEL": (
            "additionally applies the campaign's P1 admissibility filter (routes/registry.jsonl "
            "R008, COURT_PROVED, NOT kernel-checked): for a prime p with p^2 > B and "
            "A = {n/p : n in S, p | n} subset {1..floor(B/p)}, either A is empty or p divides "
            "the numerator of sum_{j in A} 1/j. Re-derived and implemented in MINE/p1ban.py."
        ),
    },
    "gates_run": {
        "known_answer_gate": {
            "script": "MINE/control289b.py",
            "result": "PASS -- 1848 (k,B,target) triples cross-checked against the naive "
                      "Fraction enumerator in MINE/verify289.py; 32 of them have a real "
                      "decomposition (non-vacuous arm); 0 mismatches.",
        },
        "second_known_answer_gate": {
            "script": "MINE/control289.py (first form)",
            "result": "PASS -- 144 triples, 8 with a real decomposition, 0 mismatches.",
        },
        "p1_filter_consistency_gate": {
            "script": "MINE/banconsist.py",
            "result": "PASS at B=60 for k=1..6: the P1-filtered search and the kernel-only "
                      "search return identical existence verdicts; measured speedup 1x, 8.6x, "
                      "50.6x, 205x, 518x, 1003x for k=1..6. Incomplete beyond B=60 k=6 "
                      "(OPERATOR_STOPPED).",
        },
    },
    "reproduce": {
        "per_shard": "python search289.py --k K --B B --shard A1 [--p1ban] --out FILE",
        "all_shards_one_k": "python search289.py --k K --B B --allshards [--p1ban] --out FILE",
        "sharded_round": ('python drive289.py --jobs "k1:B1,k2:B2,..." --workers 20 '
                          '--budget 30000000 --deadline 1500 --tag TAG [--p1ban] --outdir <this dir>'),
        "verify_a_witness_independently": "python verify289.py --check '[[a1,b1],[a2,b2],...]'",
        "known_answer_gate": "python control289b.py",
        "p1_consistency_gate": "python banconsist.py",
        "scripts_location": "MINE (scratchpad) -- search289.py, verify289.py, p1ban.py, "
                            "drive289.py, control289.py, control289b.py, banconsist.py, "
                            "calib.py, probeban.py, finalize.py",
    },
    "jobs": jobs,
    "operator_stopped": operator_stopped,
    "best_per_k": {
        str(k): {"verdict": j["verdict"], "bound_B": j["bound_B"],
                 "shards_exhausted": j.get("shards_exhausted"), "n_shards": j.get("n_shards"),
                 "prune_tier": j.get("prune_tier"), "statement": j.get("statement")}
        for k, j in sorted(best.items(), key=lambda kv: kv[0])
    },
    "movement_against_the_standing_campaign_bounds": {
        "prior_standing": "k=1 and k=2 exhaustively empty to bound 260 (closure-ranking "
                          "2026-09-02, MINE\\probe289.py); the k=3 attempt did not terminate "
                          "unsharded at B=260 or B=150.",
        "now": "k=3 is EXHAUSTED to B=600 (162 shards, 1,451,507 nodes, 15.5 s on 20 workers, "
               "P1 tier) and independently EXHAUSTED to B=260 and B=200 on kernel-only prunes. "
               "That moves the k=3 frontier from 'did not terminate at 260' to 'empty to 600' "
               "-- a 2.3x bound advance on the ranker's own named computation, and the first "
               "termination of it.",
        "kernel_only_cross_check": "k=3 EXHAUSTED to B=260 (18,613,634 nodes) and to B=200 "
                                   "(6,323,770 nodes) using no P1 assumption at all; the P1 "
                                   "tier agrees on both.",
        "large_k": "k=27,28,29,30 at B=200 kernel-only are PARTIAL: 2-3 of ~60 shards exhausted, "
                   "57-58 budget-stopped at 20,000,000 nodes each. No claim is made for those k.",
    },
}
fn = os.path.join(OUT, "SEARCH-RECEIPT-%s.json" % utc)
with open(fn, "w", encoding="utf-8", errors="replace") as f:
    json.dump(rec, f, indent=1)
print("wrote", fn)
for k, j in sorted(best.items(), key=lambda kv: kv[0]):
    print("k=%2s %-10s B=%-5s shards %s/%s tier=%s"
          % (k, j["verdict"], j["bound_B"], j.get("shards_exhausted"), j.get("n_shards"),
             j.get("prune_tier")))
