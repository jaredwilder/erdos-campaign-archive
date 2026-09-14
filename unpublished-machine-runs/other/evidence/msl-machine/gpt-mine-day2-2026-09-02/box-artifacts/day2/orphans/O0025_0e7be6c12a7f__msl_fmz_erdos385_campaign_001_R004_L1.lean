import Mathlib

set_option autoImplicit false



noncomputable section skip — plain defs:

partial def lpf : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | m =>
    (List.range (m/2 + 1)).drop 2 |>.find? (fun d => d ∣ m && d < m) |>.getD m

def isComp : Nat → Bool
  | m => 4 ≤ m ∧ lpf m < m ∧ 1 < lpf m

def bestF : Nat → Nat
  | n => ((List.range n).filter isComp).foldl (fun acc m => max acc (m + lpf m)) 0

def checkOdd : Nat → Bool
  | n => let m := n - 1; isComp m ∧ m + lpf m = n + 1 ∧ m + lpf m ≤ bestF n

def checkEven : Nat → Bool
  | n => let m := n - 2; isComp m ∧ m + lpf m = n ∧ n ≤ bestF n

def checkL1 : Nat → Bool
  | n => if n % 2 == 1 then checkOdd n else checkEven n

def checkAll : Bool := (List.range 56).all (fun i => checkL1 (i + 5))

theorem msl_fmz_erdos385_campaign_001_R004_L1  : checkAll = true := by native_decide

-- axiom footprint
#print axioms lpf
#print axioms isComp
#print axioms bestF
#print axioms checkOdd
#print axioms checkEven
#print axioms checkL1
#print axioms checkAll
#print axioms msl_fmz_erdos385_campaign_001_R004_L1
