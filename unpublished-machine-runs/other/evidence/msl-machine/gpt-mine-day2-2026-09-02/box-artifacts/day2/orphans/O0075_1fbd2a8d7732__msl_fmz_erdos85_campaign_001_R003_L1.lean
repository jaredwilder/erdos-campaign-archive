import Mathlib

set_option autoImplicit false


-- Fragment of L1, self-contained core Lean 4, all Bool/Nat:
-- (i) f(4) = 2 exactly, both directions;
-- (ii) f(10) >= 4 via explicit Petersen-graph witness.

def adj (E : List (Nat × Nat)) (a b : Nat) : Bool :=
  E.elem (a, b) || E.elem (b, a)

def deg (E : List (Nat × Nat)) (v : Nat) : Nat :=
  (E.filter (fun e => e.1 == v || e.2 == v)).length

def minDeg (E : List (Nat × Nat)) (n d : Nat) : Bool :=
  (List.range n).all (fun v => d ≤ deg E v)

def hasC4 (E : List (Nat × Nat)) (n : Nat) : Bool :=
  (List.range n).any fun a =>
  (List.range n).any fun b =>
  (List.range n).any fun c =>
  (List.range n).any fun d =>
    !(a == b) && !(a == c) && !(a == d) &&
    !(b == c) && !(b == d) && !(c == d) &&
    adj E a b && adj E b c && adj E c d && adj E d a

/-- Petersen graph. -/
def petEdges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),
   (0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def checkPetersen : Bool :=
  petEdges.length == 15 && minDeg petEdges 10 3 && !(hasC4 petEdges 10)

/-- All 64 graphs on vertices 0..3 as bitmasks over 6 edges. -/
def e4 : List (Nat × Nat) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

def maskEdges (m : Nat) : List (Nat × Nat) :=
  (e4.zipWithIndex).filterMap (fun p =>
    if m.testBit p.2 then some p.1 else none)

def checkF4upper : Bool :=
  (List.range 64).all fun m =>
    let E := maskEdges m
    !(minDeg E 4 2) || hasC4 E 4

/-- Lower witness for f(4) > 1: path P4, min degree 1, C4-free. -/
def p4 : List (Nat × Nat) := [(0,1),(1,2),(2,3)]

def checkF4lower : Bool :=
  minDeg p4 4 1 && !(hasC4 p4 4)

def checkL1 : Bool := checkPetersen && checkF4upper && checkF4lower

theorem msl_fmz_erdos85_campaign_001_R003_L1  : checkL1 = true := by native_decide

-- axiom footprint
#print axioms adj
#print axioms deg
#print axioms minDeg
#print axioms hasC4
#print axioms petEdges
#print axioms checkPetersen
#print axioms e4
#print axioms maskEdges
#print axioms checkF4upper
#print axioms p4
#print axioms checkF4lower
#print axioms checkL1
#print axioms msl_fmz_erdos85_campaign_001_R003_L1
