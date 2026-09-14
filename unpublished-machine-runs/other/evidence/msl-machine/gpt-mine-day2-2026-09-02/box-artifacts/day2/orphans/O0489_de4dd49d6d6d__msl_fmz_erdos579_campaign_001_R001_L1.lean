import Mathlib

set_option autoImplicit false


def n : Nat := 6
-- graphs on vertices 0..5 encoded by bitmask over the 15 unordered pairs
def pairIdx : List (Nat × Nat) :=
  (List.range n).flatMap (fun i => (List.range n).filterMap (fun j =>
    if i < j then some (i, j) else none))
def adj (m : Nat) (i j : Nat) : Bool :=
  if i < j then (m >>> (pairIdx.indexOf (i,j))) % 2 == 1
  else if j < i then (m >>> (pairIdx.indexOf (j,i))) % 2 == 1
  else false
def isK222 (m : Nat) (a b c d e f : Nat) : Bool :=
  adj m a d && adj m a e && adj m a f &&
  adj m b d && adj m b e && adj m b f &&
  adj m c d && adj m c e && adj m c f &&
  !(adj m a b) && !(adj m a c) && !(adj m b c) &&
  !(adj m d e) && !(adj m d f) && !(adj m e f)
def hasK222 (m : Nat) : Bool :=
  ((List.range n).flatMap (fun a => (List.range n).flatMap (fun b =>
   (List.range n).flatMap (fun c => (List.range n).flatMap (fun d =>
   (List.range n).flatMap (fun e => (List.range n).map (fun f =>
     isK222 m a b c d e f))))))).any id
def commonNbrs (m : Nat) (a b : Nat) : List Nat :=
  (List.range n).filter (fun v => adj m a v && adj m b v)
def isK22in (m : Nat) (x y u v : Nat) : Bool :=
  adj m x u && adj m x v && adj m y u && adj m y v &&
  !(adj m x y) && !(adj m u v)
def hasK22in (m : Nat) (vs : List Nat) : Bool :=
  (vs.flatMap (fun x => vs.flatMap (fun y =>
   vs.flatMap (fun u => vs.map (fun v => isK22in m x y u v))))).any id
def check_L1 : Bool :=
  (List.range (2 ^ 15)).all (fun m =>
    ((List.range n).flatMap (fun a => (List.range n).flatMap (fun b =>
      if a < b && !(adj m a b) then [a, b] else []))).all (fun ab =>
        let a := ab.head!; let b := ab.tail!.head!
        !(hasK22in m (commonNbrs m a b)) || hasK222 m))

theorem msl_fmz_erdos579_campaign_001_R001_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms n
#print axioms pairIdx
#print axioms adj
#print axioms isK222
#print axioms hasK222
#print axioms commonNbrs
#print axioms isK22in
#print axioms hasK22in
#print axioms check_L1
#print axioms msl_fmz_erdos579_campaign_001_R001_L1
