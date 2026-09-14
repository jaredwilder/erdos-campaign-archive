import Mathlib

set_option autoImplicit false


def a (n : Nat) : Nat := n * n

def ps : List Nat :=
  (List.range 200).filter (fun k => (List.range 15).any (fun n => a n == k))

def check : Bool :=
  match ps with
  | [] => false
  | _ => ps.zip ps.tail |>.all (fun p => p.2 - p.1 > 0) && (ps.head! = 0)

theorem msl_fmz_erdos260_campaign_001_R003_L1  : check = true := by decide

-- axiom footprint
#print axioms a
#print axioms ps
#print axioms check
#print axioms msl_fmz_erdos260_campaign_001_R003_L1
