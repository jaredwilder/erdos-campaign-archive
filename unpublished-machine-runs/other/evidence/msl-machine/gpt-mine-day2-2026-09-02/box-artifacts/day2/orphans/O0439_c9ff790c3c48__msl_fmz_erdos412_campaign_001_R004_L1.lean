import Mathlib

set_option autoImplicit false


def sigma (k : Nat) : Nat := (List.range (k+1)).filter (fun d => k % d == 0) |>.sum

def isPrime (k : Nat) : Bool := k >= 2 && (List.range k).drop 2 |>.all (fun d => k % d != 0)

def check_lemma (N : Nat) : Bool :=
  (List.range (N - 1)).all (fun i =>
    let k := i + 2
    (sigma k >= k + 1) && ((sigma k == k + 1) == isPrime k))

theorem msl_fmz_erdos412_campaign_001_R004_L1  : check_lemma 50 = true := by decide

-- axiom footprint
#print axioms sigma
#print axioms isPrime
#print axioms check_lemma
#print axioms msl_fmz_erdos412_campaign_001_R004_L1
