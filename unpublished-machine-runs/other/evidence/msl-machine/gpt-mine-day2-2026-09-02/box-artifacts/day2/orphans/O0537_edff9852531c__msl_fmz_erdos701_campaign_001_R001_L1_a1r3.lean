import Mathlib

set_option autoImplicit false


-- Edge (x,y) with x<y lives at bit x*4+y of the 16-bit mask.
def ebit (x y : Nat) : Nat := if x < y then 2^(x*4+y) else 2^(y*4+x)

def deg (m v : Nat) : Nat :=
  ((List.range 16).filter (fun k => k/4 < k%4 && (k/4 == v || k%4 == v)
      && ((m >>> k) % 2 == 1))).length

-- One Chvatal round: OR in every missing edge whose endpoint degree-sum is >= 4.
-- Sequential fold is sound because the condition is monotone in m.
def chvatalStep (m : Nat) : Nat :=
  (List.range 16).foldl (fun acc k =>
    if k/4 < k%4 && ((acc >>> k) % 2 == 0)
       && deg acc (k/4) + deg acc (k%4) >= 4
    then acc + 2^k else acc) m

-- 7 bounded rounds reach the fixpoint (at most 6 edges can ever be added).
def closure (m : Nat) : Nat := (List.range 7).foldl (fun acc _ => chvatalStep acc) m

def cycMask (p : List Nat) : Nat :=
  match p with
  | [a,b,c,d] => ebit a b ||| ebit b c ||| ebit c d ||| ebit d a
  | _ => 0

def perms : List (List Nat) :=
  [[0,1,2,3],[0,1,3,2],[0,2,1,3],[0,2,3,1],[0,3,1,2],[0,3,2,1],
   [1,0,2,3],[1,0,3,2],[1,2,0,3],[1,2,3,0],[1,3,0,2],[1,3,2,0],
   [2,0,1,3],[2,0,3,1],[2,1,0,3],[2,1,3,0],[2,3,0,1],[2,3,1,0],
   [3,0,1,2],[3,0,2,1],[3,1,0,2],[3,1,2,0],[3,2,0,1],[3,2,1,0]]

def hamiltonian (m : Nat) : Bool :=
  perms.any (fun p => (m &&& cycMask p) == cycMask p)

def check_L1 : Bool :=
  (List.range 64).all (fun m => hamiltonian m == (closure m == 15))
  && ((List.range 64).filter hamiltonian).length == 10

theorem msl_fmz_erdos701_campaign_001_R001_L1_a1r3  : check_L1 = true := by decide

-- axiom footprint
#print axioms ebit
#print axioms deg
#print axioms chvatalStep
#print axioms closure
#print axioms cycMask
#print axioms perms
#print axioms hamiltonian
#print axioms check_L1
#print axioms msl_fmz_erdos701_campaign_001_R001_L1_a1r3
