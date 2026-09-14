import Mathlib

set_option autoImplicit false


def Z5 : List Nat := [0, 1, 2, 3, 4]
def S5 : List Nat := [1, 4]
def Z8 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def S8 : List Nat := [1, 6]

def in5 (n : Nat) : Bool := n == 0 || n == 2 || n == 3
def in8 (n : Nat) : Bool := n == 2 || n == 4 || n == 7

def check5 : Bool :=
  Z5.all (fun x => Z5.all (fun y =>
    let s := (x + y) % 5
    (!(S5.contains s)) && in5 s))

def check8 : Bool :=
  Z8.all (fun x => Z8.all (fun y =>
    let s := (x + y) % 8
    (!(S8.contains s)) && in8 s))

def check_witness : Bool := check5 && check8

theorem msl_fmz_erdos341_campaign_001_R001_L1  : check_witness = true := by decide

-- axiom footprint
#print axioms Z5
#print axioms S5
#print axioms Z8
#print axioms S8
#print axioms in5
#print axioms in8
#print axioms check5
#print axioms check8
#print axioms check_witness
#print axioms msl_fmz_erdos341_campaign_001_R001_L1
