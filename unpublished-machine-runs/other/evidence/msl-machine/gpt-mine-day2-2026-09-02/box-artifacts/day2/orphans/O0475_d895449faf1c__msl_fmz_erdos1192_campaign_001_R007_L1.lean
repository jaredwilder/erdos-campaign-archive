import Mathlib

set_option autoImplicit false


def witnesses : List (Nat × List Nat) := [(1, [1,2]), (2, [1,2,3]), (3, [1,2,3,4]), (4, [1,2,3,4,5]), (5, [1,2,3,4,5,6])]

def sumset (A : List Nat) : List Nat :=
  (A.flatMap (fun a => A.map (fun b => a + b))).eraseDups

def covers (M : Nat) (S : List Nat) : Bool :=
  (List.range (M + 1)).all (fun k => k + 1 >= M && S.contains (k + 1) || S.contains (k + 1))

def intervalCheck (N : Nat) (A : List Nat) : Bool :=
  let S := sumset A
  -- verify every k in [N+1, 2N-1] lies in A+A, by exact integer enumeration
  (List.range N).all (fun i => S.contains (N + 1 + i)) && (N + 1 + N - 1 <= 2 * N)

def checkAll : Bool :=
  witnesses.all (fun p => intervalCheck p.1 p.2) && witnesses.length == 5

theorem msl_fmz_erdos1192_campaign_001_R007_L1  : checkAll = true := by decide

-- axiom footprint
#print axioms witnesses
#print axioms sumset
#print axioms covers
#print axioms intervalCheck
#print axioms checkAll
#print axioms msl_fmz_erdos1192_campaign_001_R007_L1
