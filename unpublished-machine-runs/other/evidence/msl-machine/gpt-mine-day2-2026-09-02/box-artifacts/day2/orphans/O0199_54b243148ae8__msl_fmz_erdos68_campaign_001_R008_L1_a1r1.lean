import Mathlib

set_option autoImplicit false


def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

def geoSum (f : Nat) : Nat :=
  (List.range 20).foldl (fun acc k => acc + f ^ k) 0

-- Exact rational certificate, all-integer after clearing the common
-- denominator D·(n!-1) with D = (n!)^20:
--   S_J   = P / (D·(n!-1)),  P = (n!-1)·Σ_{k=0}^{19} (n!)^k
--   LHS   = D / (D·(n!-1))   (the full geometric sum 1/(n!-1))
--   tail  = 1 / (D·(n!-1))
-- so S_J < LHS  ⟺  P < D  and  LHS = S_J + tail  ⟺  D = P + 1.
def checkN (n : Nat) : Bool :=
  let f := factorial n
  let D := f ^ 20
  let P := (f - 1) * geoSum f
  (f - 1 > 0) && (P < D) && (D == P + 1)

def checkAll : Bool :=
  (List.range 11).all (fun i => checkN (i + 2))

theorem msl_fmz_erdos68_campaign_001_R008_L1_a1r1  : checkAll = true := by decide

-- axiom footprint
#print axioms factorial
#print axioms geoSum
#print axioms checkN
#print axioms checkAll
#print axioms msl_fmz_erdos68_campaign_001_R008_L1_a1r1
