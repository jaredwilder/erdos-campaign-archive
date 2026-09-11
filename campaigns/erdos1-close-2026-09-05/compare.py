"""
Two receipted checks for the erdos1 CLOSE campaign.

(1) CROSSOVER.  The frozen formal-conjectures file proves
        erdos_1.variants.weaker :  (1/3) * 2^n / n  <  N
    This campaign's Lean file proves
        erdos1_sqrt            :  2^(2n) <= 64 * n * N^2, i.e.  2^n / (8*sqrt n) <= N
    Find the least n from which the second RHS strictly exceeds the first.
    (No literal is chosen and echoed: both RHS are recomputed from the formulas.)

(2) BOUNDARY / SANITY.  Evaluate `2^(2n) <= 64*n*N^2` at every exactly-known
    (n, f(n)) pair from receipts/f-of-n.json, plus the degenerate cards n = 0, 1.
"""
import json
import math
import io

with io.open("receipts/f-of-n.json", encoding="utf-8") as fh:
    fdata = json.load(fh)

# (1) crossover
cross = None
table = []
for n in range(2, 41):
    frozen = (1.0 / 3.0) * (2.0 ** n) / n
    ours = (2.0 ** n) / (8.0 * math.sqrt(n))
    row = {"n": n, "frozen_rhs": frozen, "ours_rhs": ours, "ours_stronger": ours > frozen}
    table.append(row)
    if cross is None and ours > frozen:
        cross = n

# (2) boundary evaluation on the exact f(n) table
bound_rows = []
for r in fdata["rows"]:
    n, N = r["n"], r["f_n"]
    if N is None:
        continue
    lhs = 2 ** (2 * n)
    rhs = 64 * n * N * N
    bound_rows.append({"n": n, "N_is_f_n": N, "lhs_2_2n": lhs, "rhs_64nN2": rhs,
                       "holds": lhs <= rhs})

degenerate = []
for n, N in ((0, 5), (1, 1), (1, 5)):
    lhs = 2 ** (2 * n)
    rhs = 64 * n * N * N
    degenerate.append({"card": n, "N": N, "lhs": lhs, "rhs": rhs, "holds": lhs <= rhs})

out = {
    "crossover_least_n_where_erdos1_sqrt_beats_frozen_weaker": cross,
    "crossover_table_head": table[:12],
    "bound_at_exact_f_n": bound_rows,
    "degenerate_cards": degenerate,
    "note": "degenerate card=0 row is the FALSE case: the theorem's hypothesis 2 <= A.card "
            "is load-bearing, not decoration.",
}
with io.open("receipts/compare.json", "w", encoding="utf-8") as fh:
    json.dump(out, fh, indent=1)
print(json.dumps({k: out[k] for k in
                  ("crossover_least_n_where_erdos1_sqrt_beats_frozen_weaker",
                   "degenerate_cards")}, indent=1))
for r in bound_rows:
    print(r)
print("WROTE receipts/compare.json")
