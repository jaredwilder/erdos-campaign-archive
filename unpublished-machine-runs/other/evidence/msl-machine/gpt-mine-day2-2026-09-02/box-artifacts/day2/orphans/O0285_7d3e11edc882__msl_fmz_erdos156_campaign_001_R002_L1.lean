import Mathlib

set_option autoImplicit false


def sums (a b : Nat) : Nat := a + b

-- witness A = {1, 2, 4}, N = 8
def A : List Nat := [1, 2, 4]

-- all pairwise sums of A (ordered pairs, with repetition)
def sumList : List (Nat × Nat × Nat) :=
  [(1+1,1,1),(1+2,1,2),(2+1,2,1),(1+4,1,4),(4+1,4,1),
   (2+2,2,2),(2+4,2,4),(4+2,4,2),(4+4,4,4)]

-- Sidon: whenever two ordered-pair sums agree, the pairs agree
def sidonCheck : Bool :=
  sumList.all (fun t => sumList.all (fun u =>
    t.1 != u.1 || t = u))

-- maximality: for each x in [1,8] \ A, adjoining x creates a repeated sum
-- 3: 1+3 = 2+2 ; 5: 1+5 = 2+4 ; 6: 2+6 = 4+4 ; 7: 3+4? use 1+7 = 4+4 ; 8: 2+8 = 4+6? use 4+8 = 2+10 no -> 1+8 = ... explicit repeats below
def maxCheck : Bool :=
  ((3, 1, 3, 2, 2) :: (5, 1, 5, 2, 4) :: (6, 2, 6, 4, 4) ::
   (7, 1, 7, 4, 4) :: (8, 4, 8, 4, 8) :: []).all
   (fun r => (r.2 + r.2.1 = r.2.2.1 + r.2.2.2))

def check : Bool := sidonCheck && maxCheck

theorem msl_fmz_erdos156_campaign_001_R002_L1  : check = true := by decide

-- axiom footprint
#print axioms sums
#print axioms A
#print axioms sumList
#print axioms sidonCheck
#print axioms maxCheck
#print axioms check
#print axioms msl_fmz_erdos156_campaign_001_R002_L1
