import Mathlib

set_option autoImplicit false


def hasWitness (p B n : Nat) : Bool :=
  let lo := n + 1
  let hi := n + B - 1
  (List.range (hi - lo + 1)).any (fun i =>
    (List.range (hi - lo + 1)).any (fun j =>
      (lo + i) * (lo + j) % p == 1 % p))

def B : Nat := 32
def P : Nat := 101
def coreExc : List Nat := [7, 13]

def check_core : Bool :=
  (List.range 61).all (fun n =>
    coreExc.contains n || hasWitness P B n)

theorem msl_fmz_erdos445_campaign_001_R008_L1_a1r2  : check_core = true := by native_decide

-- axiom footprint
#print axioms hasWitness
#print axioms B
#print axioms P
#print axioms coreExc
#print axioms check_core
#print axioms msl_fmz_erdos445_campaign_001_R008_L1_a1r2
