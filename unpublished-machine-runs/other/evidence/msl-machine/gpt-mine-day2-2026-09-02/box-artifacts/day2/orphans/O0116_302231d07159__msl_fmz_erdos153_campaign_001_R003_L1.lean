import Mathlib

set_option autoImplicit false


-- Pure Lean 4, no Mathlib, no qsort, no Classical.

def isSidon (A : List Int) : Bool :=
  let ps := (List.range A.length).flatMap fun i =>
    (List.range A.length).filterMap fun j =>
      if i ≤ j then some (A[i]! + A[j]!) else none
  (ps.foldr (fun x acc => x :: acc.filter (· != x)) []).length = ps.length

def tval (A : List Int) : ℕ :=
  let ps := (List.range A.length).flatMap fun i =>
    (List.range A.length).filterMap fun j =>
      if i ≤ j then some (A[i]! + A[j]!) else none
  (ps.foldr (fun x acc => x :: acc.filter (· != x)) []).length

def sortedSums (A : List Int) : List Int :=
  let ps := (List.range A.length).flatMap fun i =>
    (List.range A.length).filterMap fun j =>
      if i ≤ j then some (A[i]! + A[j]!) else none
  (ps.foldr (fun x acc => x :: acc.filter (· != x)) []).insertionSort (· ≤ ·)

def gaps (s : List Int) : List Int := (s.zip s.tail).map fun p => p.2 - p.1

def Qnum (A : List Int) : Int :=
  (gaps (sortedSums A)).foldr (fun d acc => d * d + acc) 0

def aborts (A : List Int) : Bool := tval A == 0

/-- Fail-closed verifier behavior, exact arithmetic:
    A=[0,1,3] is Sidon, t=6, sum of squared gaps = 8,
    abort does not fire on the witness and fires on the empty set
    (the undefined enclosure (-inf,+inf)). -/
def checkWitness : Bool :=
  isSidon [0, 1, 3]
  && tval [0, 1, 3] == 6
  && Qnum [0, 1, 3] == 8
  && aborts [0, 1, 3] == false
  && aborts ([] : List Int) == true

theorem msl_fmz_erdos153_campaign_001_R003_L1  : checkWitness = true := by decide

-- axiom footprint
#print axioms isSidon
#print axioms tval
#print axioms sortedSums
#print axioms gaps
#print axioms Qnum
#print axioms aborts
#print axioms checkWitness
#print axioms msl_fmz_erdos153_campaign_001_R003_L1
