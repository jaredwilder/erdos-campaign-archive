import Mathlib

set_option autoImplicit false


def inB (n : Nat) : Bool := n % 4 == 2
def inA' (n : Nat) : Bool := !(inB n)
-- order-2 basis check for A' = ℕ \ B over [0, N], under the 0 ∈ ℕ convention
def check (N : Nat) : Bool :=
  (List.range (N+1)).all fun n =>
    (List.range (n+1)).any fun i => inA' i && inA' (n - i)

theorem msl_fmz_erdos881_campaign_001_R005_L1  : check 120 = true := by decide

-- axiom footprint
#print axioms inB
#print axioms inA'
#print axioms check
#print axioms msl_fmz_erdos881_campaign_001_R005_L1
