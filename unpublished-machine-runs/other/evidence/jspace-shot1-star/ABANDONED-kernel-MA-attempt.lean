def N : Nat := 47
def QRmask : Nat := 4626135339998
def isQR (d : Nat) : Bool := QRmask.testBit d
def beats (a b : Nat) : Bool := isQR ((b + N - a) % N)
def Dcard (S : List Nat) : Nat :=
  ((List.range N).filter (fun v => S.all (fun s => beats v s))).length

-- cheap sanity
example : Dcard [] = 47 := by decide
example : Dcard [0] = 23 := by decide
example : Dcard [0,1] = 11 := by decide
example : Dcard [0,1,3] = 4 := by decide

-- the expensive one: all strictly increasing triples
set_option maxRecDepth 40000 in
theorem fact3 : ((List.range N).all fun a => (List.range N).all fun b =>
    (List.range N).all fun c => !(a < b && b < c) || (4 ≤ Dcard [a,b,c])) = true := by
  decide +kernel

/-
ABANDONED 2026-08-27.  This file does NOT compile and is kept only as a record.
`decide +kernel` over the 16,215 strictly-increasing triples, each filtering 47
vertices, reached 90% of system RAM and was killed before finishing.  The MA
counterexample is therefore computation-certified (two independent
implementations, see verify_MA_counterexample.py) and NOT kernel-certified.
Do not cite any statement in this file as proved.
-/
