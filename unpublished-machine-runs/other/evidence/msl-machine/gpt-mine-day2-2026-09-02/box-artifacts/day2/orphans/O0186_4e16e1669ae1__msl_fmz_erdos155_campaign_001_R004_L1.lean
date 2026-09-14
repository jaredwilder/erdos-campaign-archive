import Mathlib

set_option autoImplicit false


-- Decidable fragment of L1, narrowed for kernel reduction: N ≤ 4, k ≤ 2.
-- Claim checked: for all A ⊂ [1,N], B ⊂ [N+1,N+k], if A∪B is Sidon and |A| > k,
-- then every difference b-a (b∈B, a∈A, a<b) has multiplicity ≤ 1.

def sums : List Nat → List Nat
  | [] => []
  | s => s.flatMap fun x => s.flatMap fun y => if x ≤ y then [x+y] else []

def sidon (s : List Nat) : Bool :=
  (sums s).eraseDups.length == (sums s).length

def rangeTo (n : Nat) : List Nat :=
  List.range n |>.map Nat.succ

def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (subsets xs).flatMap fun s => [s, x :: s]

def diffs (A B : List Nat) : List Nat :=
  B.flatMap fun b => A.flatMap fun a => if a < b then [b - a] else []

def multOK (l : List Nat) : Bool :=
  l.all fun d => l.count d ≤ 1

def check (N k : Nat) : Bool :=
  (subsets (rangeTo N)).all fun A =>
    (subsets (List.range k |>.map fun i => N + 1 + i)).all fun B =>
      !(sidon (A ++ B) && A.length > k) || multOK (diffs A B)

theorem msl_fmz_erdos155_campaign_001_R004_L1  : check 4 2 = true := by decide

-- axiom footprint
#print axioms sums
#print axioms sidon
#print axioms rangeTo
#print axioms subsets
#print axioms diffs
#print axioms multOK
#print axioms check
#print axioms msl_fmz_erdos155_campaign_001_R004_L1
