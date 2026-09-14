import Mathlib

set_option autoImplicit false


partial def omega : Nat -> Nat | 0 => 0 | 1 => 0 | n+2 =>
  (match (2 : Nat) with | p => if p * p > n+2 then 1 else if p ∣ (n+2) then 1 + omega ((n+2)/p) else omega (n+2) ... )
-- concrete decidable form used in the check:
def factorCount (n : Nat) : Nat :=
  let rec go (m d acc : Nat) : Nat :=
    if d * d > m then (if m > 1 then acc + 1 else acc)
    else if d ∣ m then go (m / d) d (acc + 1) else go m (d+1) acc
  termination_by go m _ _ => m
  if n <= 1 then 0 else go n 2 0

def check (n : Nat) : Bool :=
  -- the interval [n, n+6) contains an integer m with 4 ∣ m and Ω(m) ≥ 3
  (List.range 6).any (fun j =>
    let m := n + j
    4 ∣ m && factorCount m >= 3)

theorem msl_fmz_erdos891_campaign_001_R004_L1  : (List.range (10000 - 9 + 1)).all (fun i => check (9 + i)) = true := by native_decide

-- axiom footprint
#print axioms omega
#print axioms factorCount
#print axioms check
#print axioms msl_fmz_erdos891_campaign_001_R004_L1
