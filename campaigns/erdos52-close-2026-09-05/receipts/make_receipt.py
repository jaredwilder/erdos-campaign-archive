"""Build the kernel receipt for the erdos52-close-2026-09-05 fragments.

Reads the Lean file and the raw `lake env lean` log fetched from the rented box and
emits receipts/kernel-receipt.json. Every field is read from a file on disk; no value
is typed in by hand except the box identity and the Mathlib revision, which are read
back from the box in the same session and pasted into BOX/MATHLIB below.
"""
import hashlib
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
CAMPAIGN = HERE.parent
REPO = CAMPAIGN.parents[4]

BOX = "root@51.158.234.15:/root/formalizer/proofs"
MATHLIB = "919544d4309104b3f19724b0e6e48c701d27948f"
TOOLCHAIN = "leanprover/lean4:v4.31.0-rc1"

CLEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(p: pathlib.Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    lean = CAMPAIGN / "lean" / "Erdos52Frag.lean"
    log = HERE / "lake-env-lean.log"
    frozen = REPO / "oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/52.lean"
    raw = REPO / "oracle/evidence/formalizer-sources/erdos/raw-erdos-52.html"

    text = log.read_text(encoding="utf-8", errors="replace")

    errors = [ln for ln in text.splitlines() if re.search(r":\s*error", ln)]
    warnings = [ln for ln in text.splitlines() if re.search(r":\s*warning", ln)]

    axioms = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        name = m.group(1)
        axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
        axioms[name] = axs

    dirty = {k: v for k, v in axioms.items() if set(v) - CLEAN_AXIOMS}
    clean = {k: v for k, v in axioms.items() if not (set(v) - CLEAN_AXIOMS)}

    # Strip block comments (/- ... -/, including /-! ... -/) and line comments before
    # looking for the token: the file's own header prose says the word "sorry", and a
    # naive substring test convicted a clean file. The axiom audit below is the real
    # test; this is the belt to its braces.
    src = lean.read_text(encoding="utf-8")
    src_nc = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    src_nc = re.sub(r"--[^\n]*", " ", src_nc)
    sorry_in_source = bool(re.search(r"\bsorry\b", src_nc))

    receipt = {
        "campaign": "erdos52-close-2026-09-05",
        "target": "Erdos Problem 52 (Erdos-Szemeredi sum-product)",
        "backend": {
            "host": BOX,
            "toolchain": TOOLCHAIN,
            "mathlib_rev": MATHLIB,
            "command": "lake env lean Erdos52Frag.lean",
        },
        "inputs": {
            "lean_file": str(lean.relative_to(REPO)).replace("\\", "/"),
            "lean_file_sha256": sha256(lean),
            "frozen_formal_source": str(frozen.relative_to(REPO)).replace("\\", "/"),
            "frozen_formal_source_sha256": sha256(frozen),
            "frozen_prose_source": str(raw.relative_to(REPO)).replace("\\", "/"),
            "frozen_prose_source_sha256": sha256(raw),
        },
        "log": {
            "path": str(log.relative_to(REPO)).replace("\\", "/"),
            "sha256": sha256(log),
            "error_lines": errors,
            "warning_lines": warnings,
        },
        "source_contains_sorry_token": sorry_in_source,
        "axiom_audit": {
            "clean_declarations": sorted(clean),
            "dirty_declarations": dirty,
            "clean_axiom_set": sorted(CLEAN_AXIOMS),
        },
        "verdict": (
            "KERNEL_CHECKED_UNIVERSAL"
            if (not errors and not dirty and not sorry_in_source and axioms)
            else "PARTIAL"
        ),
    }

    out = HERE / "kernel-receipt.json"
    out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({k: receipt[k] for k in ("verdict", "source_contains_sorry_token")}, indent=2))
    print("errors:", len(errors), "dirty:", len(dirty), "clean:", len(clean))
    print("written:", out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
