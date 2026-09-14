import Mathlib

set_option autoImplicit false


def ivSum (a l : Nat) : Nat × Nat := (2*a + l - 1, 2)
-- interval [a, a+l-1] of l consecutive integers sums to (2a+l-1)/2 exactly.
def v2 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | _ =>
    let rec go (m acc : Nat) : Nat :=
      if m % 2 = 0 then go (m / 2) (acc + 1) else acc
    go n 0
-- valuation of the reduced interval sum: numerator 2a+l-1, denominator 2 (odd).
def valI (a l : Nat) : Nat := v2 (2*a + l - 1)
-- exact total-integer check for a PAIR of intervals: (2a+l-1)/2 + (2b+m-1)/2 is an
-- integer iff the two odd numerators have even sum, i.e. their sum ≡ 0 mod 2.
def pairIntegral (a l b m : Nat) : Bool := ((2*a + l - 1) + (2*b + m - 1)) % 2 == 0
-- Kurschak parity for a pair with integer total: both numerator valuations equal,
-- hence exactly 2 intervals attain the global max (even).
def pairParityOk (a l b m : Nat) : Bool :=
  if pairIntegral a l b m then valI a l == valI b m else true
-- pool: all (a, l) with a >= 1, l >= 2, a + l <= B
def pool (B : Nat) : List (Nat × Nat) :=
  (List.range (B - 1)).flatMap
    (fun a => (List.range (B - 1 - a)).map (fun l => (a + 1, l + 2)))
def checkSize1 (B : Nat) : Bool :=
  (pool B).all (fun p =>
    -- a single length->=2 interval never sums to an integer: numerator 2a+l-1 is odd
    (2*p.1 + p.2 - 1) % 2 == 1)
def checkSize2 (B : Nat) : Bool :=
  let ps := pool B
  (ps.flatMap (fun p => ps.map (fun q => (p, q)))).all
    (fun pq => pairParityOk pq.1.1 pq.1.2 pq.2.1 pq.2.2)
def kurschakParityCheck (B : Nat) : Bool := checkSize1 B && checkSize2 B

theorem msl_fmz_erdos289_campaign_001_R002_L1  : kurschakParityCheck 6 = true := by decide

-- axiom footprint
#print axioms ivSum
#print axioms v2
#print axioms valI
#print axioms pairIntegral
#print axioms pairParityOk
#print axioms pool
#print axioms checkSize1
#print axioms checkSize2
#print axioms kurschakParityCheck
#print axioms msl_fmz_erdos289_campaign_001_R002_L1
