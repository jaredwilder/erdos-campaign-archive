import Mathlib

set_option autoImplicit false


def greedy (seed : List Nat) (N : Nat) : List Nat :=
  let rec step (seq : List Nat) (n : Nat) : List Nat :=
    if seq.length ≥ N then seq
    else
      let forbidden : Nat → Bool := fun x =>
        seq.any (fun a => seq.any (fun b => a + b = x))
      let rec next (x : Nat) : Nat :=
        if forbidden x then next (x + 1) else x
      step (seq ++ [next (seq.getLast! + 1)]) (n + 1)
  termination_by _ n => N - n
  step seed 0

def A1 : List Nat := greedy [1] 200

def check_l1 : Bool :=
  (A1.length = 200) ∧
  (List.range 200 |>.all (fun i => A1[i]! = 2*i + 1)) ∧
  (List.range 199 |>.all (fun i => A1[i+1]! - A1[i]! = 2))

theorem msl_fmz_erdos341_campaign_001_R003_L1_a3r1  : check_l1 = true := by decide

-- axiom footprint
#print axioms greedy
#print axioms A1
#print axioms check_l1
#print axioms msl_fmz_erdos341_campaign_001_R003_L1_a3r1
