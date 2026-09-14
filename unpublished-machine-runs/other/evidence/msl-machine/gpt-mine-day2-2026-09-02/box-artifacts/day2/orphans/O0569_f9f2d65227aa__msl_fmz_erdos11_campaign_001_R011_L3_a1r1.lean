import Mathlib

set_option autoImplicit false


def isSquarefree : Nat -> Bool
  | 0 => false
  | 1 => true
  | n => checkDiv 2 n
where checkDiv (d : Nat) (n : Nat) : Bool :=
  if d * d > n then true
  else if n % d == 0 then (n / d) % d != 0 && checkDiv (d+1) (n/d)
  else checkDiv (d+1) n
-- isSquarefree n = true iff no square d^2>1 divides n (exact Nat arithmetic, no floats)

def hasWitness (n : Nat) : Bool :=
  existAux 0 n
where existAux (l : Nat) (n : Nat) : Bool :=
  let p := 2 ^ l
  if p > n then false
  else if isSquarefree (n - p) then true else existAux (l+1) n
-- checks all l in Nat (l=0 included) with k = n - 2^l squarefree

def oddRange : List Nat :=
  (List.range 64).filter (fun n => n % 2 == 1 && n > 1)

def checkAll : Bool :=
  oddRange.all hasWitness

theorem msl_fmz_erdos11_campaign_001_R011_L3_a1r1  : checkAll = true := by decide

-- axiom footprint
#print axioms isSquarefree
#print axioms hasWitness
#print axioms oddRange
#print axioms checkAll
#print axioms msl_fmz_erdos11_campaign_001_R011_L3_a1r1
