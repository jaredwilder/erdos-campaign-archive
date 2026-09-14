import Mathlib

set_option autoImplicit false


def nV : Nat := 4
def numPairs : Nat := nV * (nV - 1) / 2

-- pair p < numPairs corresponds to (u,v) with u < v, lex order: p = u*(u+1)/2 + (v - u - 1)?
-- simpler: enumerate pairs explicitly.
def pairs : List (Nat × Nat) :=
  (List.range nV).flatMap (fun u => (List.range nV).filterMap (fun v =>
    if u < v then some (u, v) else none))

def isEdge (mask : Nat) (u v : Nat) : Bool :=
  pairs.idxOf? (if u <= v then (u, v) else (v, u))
  |>.map (fun i => (mask / 2^i) % 2 == 1)
  |>.getD false

def degree (mask u : Nat) : Nat :=
  (List.range nV).filter (fun v => v != u && isEdge mask u v) |>.length

def maxDeg (mask : Nat) : Nat :=
  (List.range nV).foldl (fun acc u => Nat.max acc (degree mask u)) 0

-- greedy: take lowest-index remaining vertex, delete it and its neighbors.
def greedyCount : Nat -> Nat -> List Nat -> Nat
  | 0, _, _ => 0
  | (k+1), mask, [] => 0
  | (k+1), mask, u :: rest =>
      let survivors := rest.filter (fun v => !(isEdge mask u v))
      1 + greedyCount k mask survivors

def checkMask (mask : Nat) : Bool :=
  let i := greedyCount nV mask (List.range nV)
  let d := maxDeg mask
  i * (d + 1) >= nV

def check_witness (_bound : Nat) : Bool :=
  (List.range (2^numPairs)).all checkMask

theorem msl_fmz_erdos501_campaign_001_R005_L1  : check_witness 4 = true := by decide

-- axiom footprint
#print axioms nV
#print axioms numPairs
#print axioms pairs
#print axioms isEdge
#print axioms degree
#print axioms maxDeg
#print axioms greedyCount
#print axioms checkMask
#print axioms check_witness
#print axioms msl_fmz_erdos501_campaign_001_R005_L1
