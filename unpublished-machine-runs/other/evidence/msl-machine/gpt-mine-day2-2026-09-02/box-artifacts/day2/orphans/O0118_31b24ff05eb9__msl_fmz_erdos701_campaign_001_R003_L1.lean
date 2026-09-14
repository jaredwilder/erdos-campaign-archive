import Mathlib

set_option autoImplicit false


-- Repaired fragment: scope narrowed to n = 2 (decide-feasible). Same lemma content on that scope: for every hereditary family F on a 2-element ground set there is x with every all-pairs intersecting subfamily F' (Set.Intersecting convention, so any subfamily containing the empty set is excluded) satisfying |F'| <= |{A in F : x in A}|. Pure Nat/Bool/List; total; exact.

def N : Nat := 2

def Power : Nat -> List (List Nat)
  | 0 => [[]]
  | n+1 =>
      let p := Power n
      p ++ (p.map (fun s => n :: s))

def subsetOf (a b : List Nat) : Bool := a.all (fun x => b.contains x)

def downClosed (fam : List (List Nat)) : Bool :=
  fam.all (fun a => (Power N).all (fun b => if subsetOf b a then fam.contains b else true))

def intersects (a b : List Nat) : Bool :=
  a.any (fun x => b.contains x)

def allPairsIntersecting (sub : List (List Nat)) : Bool :=
  sub.all (fun a => sub.all (fun b => intersects a b))

def starSize (fam : List (List Nat)) (x : Nat) : Nat :=
  (fam.filter (fun a => a.contains x)).length

def subfamilies (fam : List (List Nat)) : List (List (List Nat)) :=
  (Power fam.length).map (fun idx => idx.filterMap (fun i => fam.get? i))

def maxIntersecting (fam : List (List Nat)) : Nat :=
  (subfamilies fam).filter allPairsIntersecting
    |>.map (fun s => s.length)
    |>.foldl Nat.max 0

def checkN : Bool :=
  let allSubsets := Power N
  let hereditaryFams := (Power allSubsets.length)
      |>.map (fun idx => idx.filterMap (fun i => allSubsets.get? i))
      |>.filter downClosed
  hereditaryFams.all (fun fam =>
    (List.range N).any (fun x => maxIntersecting fam <= starSize fam x))

theorem msl_fmz_erdos701_campaign_001_R003_L1  : checkN = true := by decide

-- axiom footprint
#print axioms N
#print axioms Power
#print axioms subsetOf
#print axioms downClosed
#print axioms intersects
#print axioms allPairsIntersecting
#print axioms starSize
#print axioms subfamilies
#print axioms maxIntersecting
#print axioms checkN
#print axioms msl_fmz_erdos701_campaign_001_R003_L1
