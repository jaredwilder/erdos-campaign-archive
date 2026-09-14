import Mathlib

set_option autoImplicit false


def isPow2 (n : Nat) : Bool := n > 0 && 2^(Nat.log2 n) == n
def P (N : Nat) : List Nat := (List.range (N+1)).filter isPow2
def is3AP (a b c : Nat) : Bool := a + c == 2 * b
def threeAPFree (L : List Nat) : Bool :=
  !((List.range L.length).flatMap (fun i => (List.range L.length).flatMap (fun j => (List.range L.length).filter (fun k => is3AP (L[i]!) (L[j]!) (L[k]!) && i != j && j != k && i != k)))).any id
def checkLower (N : Nat) : Bool :=
  threeAPFree (P N) && ((P N).length == Nat.log2 N + 1)
def checkRange : Bool := (List.range 257).all checkLower
def checkF3_3 : Bool :=
  ((List.range 8).filter (fun m => Nat.popcount m == 3)).all (fun m =>
    !(threeAPFree ((List.range 4).filter (fun x => (m >>> x) % 2 == 1))))
def checkF3_8 : Bool :=
  ((List.range 256).filter (fun m => Nat.popcount m == 5)).all (fun m =>
    !(threeAPFree ((List.range 9).filter (fun x => (m >>> x) % 2 == 1))))
def checkAll : Bool := checkRange && checkF3_3 && checkF3_8

theorem msl_fmz_erdos535_campaign_001_R014_LOG_LOWER_F3_POWERS2_a1r3  : checkAll = true := by decide

-- axiom footprint
#print axioms isPow2
#print axioms P
#print axioms is3AP
#print axioms threeAPFree
#print axioms checkLower
#print axioms checkRange
#print axioms checkF3_3
#print axioms checkF3_8
#print axioms checkAll
#print axioms msl_fmz_erdos535_campaign_001_R014_LOG_LOWER_F3_POWERS2_a1r3
