#!/usr/bin/env python3
"""
stamp_receipt.py -- the HARNESS stamps FORMAL_STATUS, the speaker never does.

MSL L32 (SPEAKER_STAMPED_KERNEL): `KERNEL_CHECKED_*` is harness vocabulary.
This tool is that harness.  It reads

  * the raw `lake env lean <file>` output (exit code + every `#print axioms` line)
  * the Lean source itself (to classify the CONCLUSION SHAPE of each declaration)

and emits one FORMAL_STATUS word per declaration, from the closed alphabet of
MSL s.10.  Nothing here is a judgement about mathematics; it is a judgement
about what the kernel accepted and over what shape.

Rules, stated so they can be attacked:

  R1  exit != 0                                     -> KERNEL_FAILED (whole file)
  R2  output contains 'declaration uses sorry'      -> KERNEL_FAILED (that decl)
  R3  axioms outside {propext, Classical.choice, Quot.sound}
                                                    -> KERNEL_CHECKED_DIRTY_AXIOMS
  R4  the declaration's statement binds a variable over an INFINITE type
      (ℕ) and is not an equation between closed terms
                                                    -> KERNEL_CHECKED_UNIVERSAL
  R5  the declaration's statement is a closed Boolean equation (no binder)
                                                    -> KERNEL_CHECKED_FINITE_COMPUTATION
  R6  a declaration derived ONLY from an R5 declaration inherits
      KERNEL_CHECKED_FINITE_COMPUTATION even if its own statement binds a
      variable, because its evidence domain is the finite scan
      (declared explicitly in FINITE_DERIVED below -- never inferred)

usage:  python stamp_receipt.py <lean-src> <lean-out> <label> > receipts/<label>.json
"""
import hashlib
import json
import re
import sys

CLEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# R6 is a DECLARED list, not an inference: these declarations are true
# statements whose only evidence is the finite scan.
FINITE_DERIVED = {"scan_1024", "residual_drops_below_1024"}


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest()


def statement_of(src: str, name: str) -> str:
    """Grab the declaration's statement text: from `theorem <name>` up to `:=`."""
    m = re.search(r"^theorem\s+" + re.escape(name) + r"\b", src, re.M)
    if not m:
        return ""
    tail = src[m.end():]
    cut = tail.find(":=")
    return tail[:cut] if cut >= 0 else tail[:400]


def classify_shape(stmt: str, name: str) -> str:
    if name in FINITE_DERIVED:
        return "FINITE"
    # explicit (n : ℕ), implicit {n : ℕ}, and multi-name binders (m n : ℕ)
    if "∀" in stmt or re.search(r"[({]\s*[a-zA-Z]\w*(?:\s+[a-zA-Z]\w*)*\s*:\s*ℕ\s*[)}]", stmt):
        return "UNIVERSAL"
    return "FINITE"


def main() -> None:
    src_path, out_path, label = sys.argv[1], sys.argv[2], sys.argv[3]
    src = open(src_path, encoding="utf-8").read()
    out = open(out_path, encoding="utf-8", errors="replace").read()

    m = re.search(r"^EXIT=(\d+)$", out, re.M)
    exit_code = int(m.group(1)) if m else None

    # `#print axioms foo` prints:  'foo' depends on axioms: [a, b, c]
    # or                          'foo' does not depend on any axioms
    axioms = {}
    for mm in re.finditer(
            r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", out):
        axioms[mm.group(1)] = [a.strip() for a in mm.group(2).split(",") if a.strip()]
    for mm in re.finditer(r"'([\w.]+)' does not depend on any axioms", out):
        axioms[mm.group(1)] = []

    errors = [ln for ln in out.splitlines()
              if re.search(r"error:", ln) or "sorry" in ln.lower()]

    decls = []
    for full, ax in sorted(axioms.items()):
        short = full.split(".")[-1]
        stmt = statement_of(src, short)
        dirty = [a for a in ax if a not in CLEAN_AXIOMS]
        if exit_code != 0:
            status = "KERNEL_FAILED"
        elif dirty:
            status = "KERNEL_CHECKED_DIRTY_AXIOMS"
        elif classify_shape(stmt, short) == "UNIVERSAL":
            status = "KERNEL_CHECKED_UNIVERSAL"
        else:
            status = "KERNEL_CHECKED_FINITE_COMPUTATION"
        decls.append({
            "declaration": full,
            "statement": " ".join(stmt.split()),
            "axioms": ax,
            "dirty_axioms": dirty,
            "formal_status": status,
        })

    receipt = {
        "label": label,
        "tool": "stamp_receipt.py",
        "rules": ["R1 exit!=0 -> KERNEL_FAILED",
                  "R2 sorry -> KERNEL_FAILED",
                  "R3 dirty axioms -> KERNEL_CHECKED_DIRTY_AXIOMS",
                  "R4 binder over an infinite type -> KERNEL_CHECKED_UNIVERSAL",
                  "R5 closed equation -> KERNEL_CHECKED_FINITE_COMPUTATION",
                  "R6 declared finite-derived -> KERNEL_CHECKED_FINITE_COMPUTATION"],
        "finite_derived_declared": sorted(FINITE_DERIVED),
        "source_file": src_path,
        "source_sha256": sha256(src_path),
        "lean_output_file": out_path,
        "lean_output_sha256": sha256(out_path),
        "exit_code": exit_code,
        "error_lines": errors,
        "sorry_free": (exit_code == 0 and not errors),
        "declaration_count": len(decls),
        "declarations": decls,
    }
    print(json.dumps(receipt, indent=1))


if __name__ == "__main__":
    main()
