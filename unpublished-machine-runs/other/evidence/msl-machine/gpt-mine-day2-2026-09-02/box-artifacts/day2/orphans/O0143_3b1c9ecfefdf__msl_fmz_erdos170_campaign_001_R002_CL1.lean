import Mathlib

set_option autoImplicit false


def check_cl1 : Bool :=
  -- Part 1: ten distinct diffs in [1,10] must be exactly 1..10; their sum is 55 (odd).
  let s : Nat := (List.range 10).foldl (fun acc n => acc + (n + 1)) 0
  -- Part 2: gap-weighted sum 4*d1+6*d2+6*d3+4*d4 is even for ALL integers d1..d4;
  -- parity depends only on d_i mod 2, so exhaustively check the 16 parity classes.
  let part2 : Bool := (List.range 16).all (fun q =>
    let d1 : Nat := q / 8 % 2
    let d2 : Nat := q / 4 % 2
    let d3 : Nat := q / 2 % 2
    let d4 : Nat := q % 2
    (4 * d1 + 6 * d2 + 6 * d3 + 4 * d4) % 2 == 0)
  (s == 55) && part2

theorem msl_fmz_erdos170_campaign_001_R002_CL1  : check_cl1 = true := by decide

-- axiom footprint
#print axioms check_cl1
#print axioms msl_fmz_erdos170_campaign_001_R002_CL1
