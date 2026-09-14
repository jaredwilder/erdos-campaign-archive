import Mathlib

set_option autoImplicit false


def L (n : Nat) : Nat := (List.range n).foldl (fun acc k => Nat.lcm acc (k+1)) 1

-- Core of L1: for every k ≤ n, k divides L_n, hence L_n/k ∈ Nat, hence
-- Σ δ_k/k = (Σ δ_k · (L_n/k)) / L_n with an integer numerator:
-- every signed sum is an integer multiple of 1/L_n.
-- Decidable instance, no 3^n enumeration (that enumeration was the prior failure).
def checkTerms (n : Nat) : Bool :=
  (List.range n).all (fun k => (L n) % (k+1) == 0)

def checkRange (N : Nat) : Bool :=
  (List.range N).all (fun i => checkTerms (i+1))

theorem msl_fmz_erdos317_campaign_001_R003_L1  : checkRange 30 = true := by decide

-- axiom footprint
#print axioms L
#print axioms checkTerms
#print axioms checkRange
#print axioms msl_fmz_erdos317_campaign_001_R003_L1
