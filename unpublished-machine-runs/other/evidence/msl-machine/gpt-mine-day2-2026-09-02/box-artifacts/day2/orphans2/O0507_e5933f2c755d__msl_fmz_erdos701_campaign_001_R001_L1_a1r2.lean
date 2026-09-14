import Mathlib

set_option autoImplicit false

namespace Day2Wrap


-- Bit k = edge (k/4, k%4), only k with k/4 < k%4 used (upper triangle).
def hasEdge (m k : Nat) : Bool := (m >>> k) % 2 == 1

def deg (m v : Nat) : Nat :=
  (List.range 16).filter (fun k => k/4 < k%4 && (k/4 == v || k%4 == v) && hasEdge m k) |>.length

def chvatalStep (m : Nat) : Nat :=
  ((List.range 16).filter (fun k => k/4 < k%4 && !(hasEdge m k) &&
      deg m (k/4) + deg m (k%4) >= 4)
   |>.foldl (fun acc k => acc + 2^k) m)

-- Bounded iteration: at most 6 edges can ever be added (upper triangle has 6 slots),
-- so 7 rounds reach the fixpoint. Total by construction, no recursion needed.
def closure (m : Nat) : Nat := (List.range 7).foldl (fun acc _ => chvatalStep acc) m

def isK4 (m : Nat) : Bool := closure m == 15

def cycEdges (c : List Nat) : List Nat :=
  (List.range 4).map (fun i =>
    let a := c[i]!; let b := c[(i+1)%4]!
    if a < b then a*4+b else b*4+a)

def allEdgeBits : List Nat := (List.range 16).filter (fun k => k/4 < k%4)

def hamiltonian (m : Nat) : Bool :=
  let E := allEdgeBits.filter (hasEdge m)
  let cycles : List (List Nat) :=
    [[0,1,2,3],[0,1,3,2],[0,2,1,3],[0,2,3,1],[0,3,1,2],[0,3,2,1],
     [1,0,2,3],[1,0,3,2],[1,2,0,3],[1,2,3,0],[1,3,0,2],[1,3,2,0],
     [2,0,1,3],[2,0,3,1],[2,1,0,3],[2,1,3,0],[2,3,0,1],[2,3,1,0],
     [3,0,1,2],[3,0,2,1],[3,1,0,2],[3,1,2,0],[3,2,0,1],[3,2,1,0]]
  cycles.any (fun c => (cycEdges c).all E.contains)

def check_L1 : Bool :=
  let ham := (List.range 64).filter hamiltonian
  (List.range 64).all (fun m => hamiltonian m == isK4 m)
  && ham.length == 10
  && ham.contains 15                       -- K4
  && ((List.range 64).filter (fun m => hamiltonian m && deg m 0 + deg m 1 + deg m 2 + deg m 3 == 5)).length == 6   -- six K4−e
  && ((List.range 64).filter (fun m => hamiltonian m && deg m 0 + deg m 1 + deg m 2 + deg m 3 == 4 && !(m == 15))).length == 3  -- three C4

theorem msl_fmz_erdos701_campaign_001_R001_L1_a1r2  : check_L1 = true := by native_decide

end Day2Wrap
-- axiom footprint
#print axioms Day2Wrap.hasEdge
#print axioms Day2Wrap.deg
#print axioms Day2Wrap.chvatalStep
#print axioms Day2Wrap.closure
#print axioms Day2Wrap.isK4
#print axioms Day2Wrap.cycEdges
#print axioms Day2Wrap.allEdgeBits
#print axioms Day2Wrap.hamiltonian
#print axioms Day2Wrap.check_L1
#print axioms Day2Wrap.msl_fmz_erdos701_campaign_001_R001_L1_a1r2
