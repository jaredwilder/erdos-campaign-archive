import Mathlib

set_option autoImplicit false


def isPow2 (n : Nat) : Bool := n > 0 && (Nat.log2 n)^2 == n
def P (N : Nat) : List Nat := (List.range (N+1)).filter isPow2
def is3AP (a b c : Nat) : Bool := a + c == 2 * b
def threeAPFree (L : List Nat) : Bool :=
  !((List.range L.length).flatMap (fun i => (List.range L.length).flatMap (fun j => (List.range L.length).filter (fun k => is3AP (L[i]!) (L[j]!) (L[k]!) && i != j && j != k && i != k)))).any (fun _ => true)
def checkLower (N : Nat) : Bool :=
  threeAPFree (P N) && ((P N).length == Nat.log2 N + 1)
def checkSmallExtremal : Bool :=
  ((List.range 8).filter (fun m => Nat.popcount m == 3)).all (fun m =>
    let L := (List.range 4).filter (fun x => (m >>> x) % 2 == 1)
    !(threeAPFree L)) &&
  ((List.range 256).filter (fun m => Nat.popcount m == 5)).all (fun m =>
    let L := (List.range 9).filter (fun x => (m >>> x) % 2 == 1)
    !(threeAPFree L))
def checkAll : Bool :=
  ((List.range (2^20 + 1)).all checkLower) && checkSmallExtremal

theorem msl_fmz_erdos535_campaign_001_R014_LOG_LOWER_F3_POWERS2_a1r2  : checkAll = true := by native_decide

-- axiom footprint
#print axioms isPow2
#print axioms P
#print axioms is3AP
#print axioms threeAPFree
#print axioms checkLower
#print axioms checkSmallExtremal
#print axioms checkAll
#print axioms msl_fmz_erdos535_campaign_001_R014_LOG_LOWER_F3_POWERS2_a1r2
