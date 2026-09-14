import Mathlib

set_option autoImplicit false


namespace Syl

def minFactors : Nat -> Nat -> List Nat
  | _, 0 => []
  | _, 1 => []
  | d, m =>
      if d * d > m then [m]
      else if m % d == 0 then d :: minFactors d (m / d)
      else minFactors (d + 1) m

def factors (n : Nat) : List Nat := minFactors 2 n

def P (n : Nat) : Nat :=
  match factors n with
  | [] => 0
  | xs => xs.getLast (by cases xs <;> simp)

def binom' (n k : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

def J (n k : Nat) : Nat := min k (n - k)

def sylvCheck (n k : Nat) : Bool :=
  let j := J n k
  if j == 0 then true
  else P (binom' n j) >= j

def checkRange (N : Nat) : Bool :=
  (List.range (N + 1)).all fun n =>
    (List.range (n + 1)).all fun k =>
      if k == 0 then true else sylvCheck n k

def check_witness : Bool := checkRange 200

end Syl

theorem msl_fmz_erdos683_campaign_001_R005_L1  : Syl.check_witness = true := by native_decide

-- axiom footprint
#print axioms Syl.minFactors
#print axioms Syl.factors
#print axioms Syl.P
#print axioms Syl.binom'
#print axioms Syl.J
#print axioms Syl.sylvCheck
#print axioms Syl.checkRange
#print axioms Syl.check_witness
#print axioms msl_fmz_erdos683_campaign_001_R005_L1
