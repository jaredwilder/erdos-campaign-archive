import Mathlib

set_option autoImplicit false


-- Vertices of the 5-cube
abbrev V := Fin 5 → Fin 2

-- The constant tensor T = 1 on the cube: its support is all of V.
def constSupport : V → Bool := fun _ => true

-- A 4-subcube: fix coordinate i to value b.
def fourCube (i : Fin 5) (b : Fin 2) : V → Bool := fun x => x i == b

-- All 10 four-subcubes, as (i, b) pairs.
def allPairs : List (Fin 5 × Fin 2) :=
  (List.finRange 5).flatMap (fun i => (List.finRange 2).map (fun b => (i, b)))

-- Check: every four-subcube fails to CONTAIN the full support, i.e. for each (i,b)
-- there is a vertex x with constSupport x = true but fourCube i b x = false
-- (take x with x i = 1 - b, explicitly built).
def missedVertex (i : Fin 5) (b : Fin 2) : V :=
  fun j => if j = i then (if b = 0 then (1 : Fin 2) else 0) else 0

def checkOne (p : Fin 5 × Fin 2) : Bool :=
  constSupport (missedVertex p.1 p.2) && !(fourCube p.1 p.2 (missedVertex p.1 p.2))

def checkRefutation : Bool := List.all allPairs checkOne

theorem msl_fmz_erdos949_campaign_001_R013_L1  : checkRefutation = true ∧ (List.length allPairs = 10) := by decide

-- axiom footprint
#print axioms V
#print axioms constSupport
#print axioms fourCube
#print axioms allPairs
#print axioms missedVertex
#print axioms checkOne
#print axioms checkRefutation
#print axioms msl_fmz_erdos949_campaign_001_R013_L1
