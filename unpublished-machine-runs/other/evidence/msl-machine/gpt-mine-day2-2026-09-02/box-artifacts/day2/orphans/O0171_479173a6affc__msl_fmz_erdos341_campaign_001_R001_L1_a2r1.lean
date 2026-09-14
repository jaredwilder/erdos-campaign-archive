import Mathlib

set_option autoImplicit false


def S5 : List Nat := [1, 4]
def S8 : List Nat := [1, 6]
def sumsetClosed (m : Nat) (S : List Nat) : Bool :=
  (S.all (fun a => S.all (fun b => let c := (a + b) % m; !(S.elem c))))

def check_lemma : Bool :=
  sumsetClosed 5 S5 && sumsetClosed 8 S8

theorem msl_fmz_erdos341_campaign_001_R001_L1_a2r1  : check_lemma = true := by decide

-- axiom footprint
#print axioms S5
#print axioms S8
#print axioms sumsetClosed
#print axioms check_lemma
#print axioms msl_fmz_erdos341_campaign_001_R001_L1_a2r1
