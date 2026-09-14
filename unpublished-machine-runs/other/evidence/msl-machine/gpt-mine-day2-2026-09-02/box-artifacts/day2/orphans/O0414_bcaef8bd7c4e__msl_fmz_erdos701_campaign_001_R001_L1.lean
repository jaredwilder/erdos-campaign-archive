import Mathlib

set_option autoImplicit false


-- Complete, self-contained Lean 4. All defs total and computable on Nat/Bool.

def isEdge (m : Nat) (u v : Nat) : Bool := m &&& 2^(u*4+v) != 0

def setEdge (m : Nat) (u v : Nat) : Nat := m ||| 2^(u*4+v) ||| 2^(v*4+u)

def deg (m : Nat) (u : Nat) : Nat :=
  ((List.range 4).filter (fun v => v != u && isEdge m u v)).length

def closureStep (m : Nat) : Nat :=
  (List.range 4).foldl (fun m u =>
    (List.range 4).foldl (fun m v =>
      if u < v && !(isEdge m u v) && (deg m u + deg m v) >= 4 then setEdge m u v else m) m) m

def closureN (m : Nat) : Nat -> Nat
  | 0 => m
  | (k+1) => closureN (closureStep m) k

def fullMask : Nat := 31710  -- bits (u,v) and (v,u) set for all u≠v: 2*(1+2+4+8+16+32)*... encodes all 12 ordered pairs

def isK4 (m : Nat) : Bool := closureN m 16 == fullMask

def perms4 : List (List Nat) :=
  [[0,1,2,3],[0,1,3,2],[0,2,1,3],[0,2,3,1],[0,3,1,2],[0,3,2,1],
   [1,0,2,3],[1,0,3,2],[1,2,0,3],[1,2,3,0],[1,3,0,2],[1,3,2,0],
   [2,0,1,3],[2,0,3,1],[2,1,0,3],[2,1,3,0],[2,3,0,1],[2,3,1,0],
   [3,0,1,2],[3,0,2,1],[3,1,0,2],[3,1,2,0],[3,2,0,1],[3,2,1,0]]

def ham (m : Nat) : Bool :=
  perms4.any (fun p =>
    isEdge m (p[0]!) (p[1]!) && isEdge m (p[1]!) (p[2]!) &&
    isEdge m (p[2]!) (p[3]!) && isEdge m (p[3]!) (p[0]!))

def iffCount : Bool :=
  (List.range 64).all (fun m => isK4 m == ham m)

def hamCount : Nat := ((List.range 64).filter ham).length

def k4Count : Nat := ((List.range 64).filter isK4).length

def lemmaL1check : Bool := iffCount && hamCount == 10 && k4Count == 10

theorem msl_fmz_erdos701_campaign_001_R001_L1  : lemmaL1check = true := by decide

-- axiom footprint
#print axioms isEdge
#print axioms setEdge
#print axioms deg
#print axioms closureStep
#print axioms closureN
#print axioms fullMask
#print axioms isK4
#print axioms perms4
#print axioms ham
#print axioms iffCount
#print axioms hamCount
#print axioms k4Count
#print axioms lemmaL1check
#print axioms msl_fmz_erdos701_campaign_001_R001_L1
