import Mathlib

set_option autoImplicit false


def sfAux : Nat → Nat → Bool
  | k, d => if d * d > k then true else if k % (d * d) == 0 then false else sfAux k (d + 1)

def squarefreeCheck (k : Nat) : Bool := sfAux k 2

def check (n : Nat) : Bool :=
  (List.range 6).any (fun l =>
    let p := 2 ^ l
    if p < n then squarefreeCheck (n - p) else false)

def targets : List Nat :=
  (List.range 60).filter (fun n => n % 2 == 1 && n > 1)

def check_all : Bool := targets.all check

theorem msl_fmz_erdos11_campaign_001_R008_L1  : check_all = true := by decide

-- axiom footprint
#print axioms sfAux
#print axioms squarefreeCheck
#print axioms check
#print axioms targets
#print axioms check_all
#print axioms msl_fmz_erdos11_campaign_001_R008_L1
