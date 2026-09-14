import Mathlib

set_option autoImplicit false


def monoAP4 (x : List Nat) : Bool :=
  (List.range x.length).any fun i =>
    (List.range x.length).any fun j =>
      (List.range x.length).any fun k =>
        (List.range x.length).any fun l =>
          (i < j && j < k && k < l) &&
          ((x.getD j 0 : Int) - (x.getD i 0 : Int) == (x.getD k 0 : Int) - (x.getD j 0 : Int)) &&
          ((x.getD k 0 : Int) - (x.getD j 0 : Int) == (x.getD l 0 : Int) - (x.getD k 0 : Int))

def isPermOf (x : List Nat) (N : Nat) : Bool :=
  (x.length == N) && ((List.range N).all (fun v => x.contains v)) && (x.eraseDups.length == N)

def VALID (N : Nat) : Bool :=
  (List.range N).permutationsList.all
    (fun p => isPermOf p N && !(monoAP4 p || monoAP4 p.reverse))

theorem msl_fmz_erdos196_campaign_001_R005_L1  : monoAP4 [1,2,3,4] = true ∧ monoAP4 [1,3,2,4] = false ∧ monoAP4 (List.reverse [1,2,3,4]) = true ∧ VALID 3 = true ∧ VALID 4 = true := by decide

-- axiom footprint
#print axioms monoAP4
#print axioms isPermOf
#print axioms VALID
#print axioms msl_fmz_erdos196_campaign_001_R005_L1
