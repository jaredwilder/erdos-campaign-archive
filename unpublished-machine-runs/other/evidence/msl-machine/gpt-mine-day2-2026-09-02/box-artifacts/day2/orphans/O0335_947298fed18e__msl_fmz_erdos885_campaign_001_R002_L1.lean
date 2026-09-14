import Mathlib

set_option autoImplicit false


def isSq (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r == n

def inD (N d : Nat) : Bool :=
  (List.range (N + 1)).any (fun a =>
    a > 0 && N % a == 0 && (a - N / a) == d || (N / a - a) == d)

def rootOf (N d : Nat) : Nat := (Nat.sqrt (d*d + 4*N) - d) / 2

def checkL1 (nMax dMax : Nat) : Bool :=
  (List.range (nMax + 1)).all (fun N =>
    if N == 0 then true else
    (List.range (dMax + 1)).all (fun d =>
      (inD N d == isSq (d*d + 4*N)) &&
      (if isSq (d*d + 4*N) then rootOf N d * (rootOf N d + d) == N else true)))

theorem msl_fmz_erdos885_campaign_001_R002_L1  : checkL1 12 12 = true := by native_decide

-- axiom footprint
#print axioms isSq
#print axioms inD
#print axioms rootOf
#print axioms checkL1
#print axioms msl_fmz_erdos885_campaign_001_R002_L1
