import Mathlib

set_option autoImplicit false



def SidonSums (A : List Nat) : List Nat := (A.flatMap fun a => A.map fun b => a + b).eraseDups

def isSidon (A : List Nat) : Bool :=
  ((A.flatMap fun a => (A.filter fun b => b ≤ a).map fun b => a + b)).eraseDups.length ==
  (A.flatMap fun a => (A.filter fun b => b ≤ a).map fun b => a + b)).length

def gapSqSum (A : List Nat) : Nat :=
  let s := A.mergeSort (· ≤ ·)
  (s.zip (s.drop 1)).foldr (fun p acc => (p.2 - p.1)^2 + acc) 0

def Q (A : List Nat) : ℚ :=
  ((gapSqSum A : ℚ)) / ((SidonSums A).length - 1 : ℚ)

def subsets4 : List (List Nat) :=
  (List.range 13).sublists4 -- realized as explicit comprehension below
  -- concretely: all [a,b,c,d] with 0 ≤ a < b < c < d ≤ 12

def subsets4' : List (List Nat) :=
  (List.range 13).flatMap fun a =>
  ((List.range 13).filter (· > a)).flatMap fun b =>
  ((List.range 13).filter (· > b)).flatMap fun c =>
  ((List.range 13).filter (· > c)).map fun d => [a, b, c, d]

def min0 (A : List Nat) : Bool := A.head! == 0

def check_minQ2 : Bool :=
  (subsets4'.all fun A => isSidon A && min0 A → (Q A ≥ 2))

def check_extremizer : Bool :=
  isSidon [0,1,4,6] && min0 [0,1,4,6] && (Q [0,1,4,6] == 2)

def check_L1 : Bool := check_minQ2 && check_extremizer

theorem msl_fmz_erdos153_campaign_001_R006_L1_a1r1  : check_L1 = true := by native_decide

-- axiom footprint
#print axioms SidonSums
#print axioms isSidon
#print axioms gapSqSum
#print axioms Q
#print axioms subsets4
#print axioms subsets4'
#print axioms min0
#print axioms check_minQ2
#print axioms check_extremizer
#print axioms check_L1
#print axioms msl_fmz_erdos153_campaign_001_R006_L1_a1r1
