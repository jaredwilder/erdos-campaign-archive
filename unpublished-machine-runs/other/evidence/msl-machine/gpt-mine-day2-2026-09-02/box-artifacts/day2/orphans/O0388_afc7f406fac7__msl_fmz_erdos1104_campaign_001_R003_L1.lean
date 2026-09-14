import Mathlib

set_option autoImplicit false



def edgeList : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),              -- cycle C5 on vertices 0..4
   (5,1),(5,4),(6,0),(6,2),(7,1),(7,3),        -- shadow u_i = 5+i ~ v_{i±1} (Mycielski)
   (8,2),(8,4),(9,0),(9,3),
   (10,5),(10,6),(10,7),(10,8),(10,9)]         -- apex 10 ~ all shadows

def adj (a b : Nat) : Bool := edgeList.contains (a,b) || edgeList.contains (b,a)

def triangleFree : Bool :=
  ((List.range 11).flatMap fun a =>
   (List.range 11).flatMap fun b =>
   (List.range 11).map fun c => (a,b,c)).all
    (fun t => match t with | (a,b,c) => !(adj a b && adj b c && adj a c))

def toF (n : Nat) : Fin 11 := ⟨n % 11, Nat.mod_lt _ (by omega)⟩

def properF (f : Fin 11 → Fin 3) : Bool :=
  edgeList.all (fun e => f (toF e.1) != f (toF e.2))

def no3Col : Prop := ¬ ∃ f : Fin 11 → Fin 3, properF f = true

instance : Decidable no3Col :=
  inferInstanceAs (Decidable (∃ f : Fin 11 → Fin 3, properF f = true))

theorem msl_fmz_erdos1104_campaign_001_R003_L1  : triangleFree = true ∧ no3Col := by native_decide

-- axiom footprint
#print axioms edgeList
#print axioms adj
#print axioms triangleFree
#print axioms toF
#print axioms properF
#print axioms no3Col
#print axioms msl_fmz_erdos1104_campaign_001_R003_L1
