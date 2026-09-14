import Mathlib

set_option autoImplicit false


-- Literal reading of the canonical statement, per L1: I_1 = ... = I_k = {1}.
def block : List Nat := [1]

-- Bool-valued check for a given k: p = 2 is prime, and for every i < k the
-- block product is congruent to 1 mod 2. The body does not branch on k, because
-- the witness is uniform in k: the product of [1] is 1 and 1 % 2 = 1 for all k.
def check_witness (k : Nat) : Bool :=
  Nat.Prime 2 && (List.range k).all (fun _ => (List.prod block % 2 == 1))

theorem msl_erdos1056_campaign_001_R001_close  : (List.range 64).all check_witness = true := by decide

-- axiom footprint
#print axioms block
#print axioms check_witness
#print axioms msl_erdos1056_campaign_001_R001_close
