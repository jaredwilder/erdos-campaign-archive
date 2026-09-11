#!/usr/bin/env python3
"""Independent re-verification FROM THE DEFINITION of a claimed (12,5,2) cover.
Shares no code with the C decider: reads its JSON, expands blocks into pairs.
"""
import sys, json, itertools
d = json.load(open(sys.argv[1]))
if "cover" not in d:
    print(json.dumps({"file": sys.argv[1], "no_cover_in_output": True,
                      "verdict": d.get("verdict"), "search_nodes": d.get("search_nodes")}))
    raise SystemExit(0)
C = [tuple(b) for b in d["cover"]]
need = set(itertools.combinations(range(12), 2))
got = set()
bad = []
for b in C:
    if len(set(b)) != 5 or not all(0 <= v < 12 for v in b):
        bad.append(list(b))
    for p in itertools.combinations(sorted(set(b)), 2):
        got.add(p)
print(json.dumps({"file": sys.argv[1], "blocks": len(C), "malformed_blocks": bad,
                  "covers_all_66_pairs": need <= got,
                  "missing": sorted(need - got)}, indent=2))
