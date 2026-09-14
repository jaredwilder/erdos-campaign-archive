import Mathlib

set_option autoImplicit false


def natMin (x y : Nat) : Nat := if x <= y then x else y

def splitAt (n a : Nat) : Option (Prod Nat Nat) :=
  if a == 0 then none
  else if n % a == 0 && Nat.gcd a (n / a) == 1 then some (a, n / a) else none

def splits (n : Nat) : List (Prod Nat Nat) :=
  List.filterMap (fun a => splitAt n a) (List.range (n + 1))

def crtRes (a b : Nat) : Nat :=
  List.headD (List.filter (fun r => r % a == 0 && (r + 1) % b == 0) (List.range (a * b))) 0

def classRes (n : Nat) : List Nat :=
  List.map (fun p => crtRes p.1 p.2) (splits n)

def countBF (n T : Nat) : Nat :=
  List.length (List.filter (fun m => (m * (m + 1)) % n == 0) (List.map (fun j => j + 1) (List.range T)))

def countDec (n T : Nat) : Nat :=
  List.foldl (fun acc r => acc + List.length (List.filter (fun m => m % n == r) (List.map (fun j => j + 1) (List.range T)))) 0 (classRes n)

def t2BF (n : Nat) : Nat :=
  List.headD (List.filter (fun m => (m * (m + 1)) % n == 0) (List.map (fun j => j + 1) (List.range (n + 2)))) (n + 1)

def t2Dec (n : Nat) : Nat :=
  List.foldl (fun acc r => natMin acc (if r == 0 then n else r)) n (classRes n)

def checkPair (n T : Nat) : Bool := countBF n T == countDec n T

def checkT2 (n : Nat) : Bool := t2BF n == t2Dec n

def checkAll (N M : Nat) : Bool :=
  List.all (List.range N) (fun i =>
    checkT2 (i + 1) && List.all (List.range M) (fun j => checkPair (i + 1) (j + 1)))

theorem msl_fmz_erdos394_campaign_001_R004_L1  : checkAll 32 32 = true := by decide

-- axiom footprint
#print axioms natMin
#print axioms splitAt
#print axioms splits
#print axioms crtRes
#print axioms classRes
#print axioms countBF
#print axioms countDec
#print axioms t2BF
#print axioms t2Dec
#print axioms checkPair
#print axioms checkT2
#print axioms checkAll
#print axioms msl_fmz_erdos394_campaign_001_R004_L1
