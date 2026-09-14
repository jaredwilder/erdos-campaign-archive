import Mathlib

set_option autoImplicit false


def omegaDistinct (n : Nat) : Nat := (n_factors n).eraseDups.length  -- distinct prime factors
-- concrete total Bool-valued realization:
def factors (n : Nat) : List Nat :=
  let rec go (d : Nat) (m : Nat) : List Nat :=
    if m ≤ 1 then []
    else if d * d > m then [m]
    else if m % d == 0 then d :: go d (m / d)
    else go (d + 1) m
  go 2 n

def omega (n : Nat) : Nat := (factors n).eraseDups.length

def checkPowersOfTwo (bound : Nat) : Bool :=
  (List.range bound |>.map (fun a => omega (2 ^ (a + 1))) |>.all (fun w => w == 1))
  && (List.range bound |>.map (fun a => (factors (2 ^ (a + 1))).eraseDups) |>.all (fun l => l == [2]))

theorem msl_fmz_erdos890_campaign_001_R002_L1  : checkPowersOfTwo 40 = true := by decide

-- axiom footprint
#print axioms omegaDistinct
#print axioms factors
#print axioms omega
#print axioms checkPowersOfTwo
#print axioms msl_fmz_erdos890_campaign_001_R002_L1
