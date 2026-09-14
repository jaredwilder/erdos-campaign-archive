import Mathlib

set_option autoImplicit false


def hasWitness (p B n : Nat) : Bool :=
  let lo := n + 1
  let hi := n + B - 1
  (List.range (hi - lo + 1)).any (fun i =>
    (List.range (hi - lo + 1)).any (fun j =>
      let a := lo + i
      let b := lo + j
      (a * b) % p == 1 % p))

def failSet (p B maxN : Nat) : List Nat :=
  (List.range (maxN + 1)).filter (fun n => !(hasWitness p B n))

def B : Nat := 32  -- exact integer proxy for p^c with p=101, c=3/4: 31 < 101^(3/4) < 32, strict-interval witnesses certified at the exact integer bound B=32

def check_core : Bool :=
  failSet 101 B 200 == [7, 13]

theorem msl_fmz_erdos445_campaign_001_R008_L1_a1r1  : check_core = true := by decide

-- axiom footprint
#print axioms hasWitness
#print axioms failSet
#print axioms B
#print axioms check_core
#print axioms msl_fmz_erdos445_campaign_001_R008_L1_a1r1
