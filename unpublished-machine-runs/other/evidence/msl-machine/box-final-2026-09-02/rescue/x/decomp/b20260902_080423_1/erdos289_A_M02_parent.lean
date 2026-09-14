import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset
open Filter

-- campaign vocabulary, already kernel-checked (msl_decompose)
def runSum (a b : ℕ) : ℚ := ∑ n ∈ Icc a b, (1 : ℚ) / n

def runProd (a b : ℕ) : ℕ := ∏ n ∈ Icc a b, n

def runNum (a b : ℕ) : ℕ := ∑ n ∈ Icc a b, runProd a b / n

-- proposed definitions

def extendHead {m : Nat} (J : Fin m -> Nat x Nat) : Fin (m + 1) -> Nat x Nat :=
  fun i => Fin.cases (2, 3) (fun j => J j) i

def tailOK (m : Nat) (J : Fin m -> Nat x Nat) : Prop :=
  (Forall i, 5 <= (J i).1 /\ (J i).1 + 1 < (J i).2) /\
  (Forall i j, i != j -> (J i).2 < (J j).1 \/ (J j).2 < (J i).1)

def fullOK (k : Nat) (I : Fin k -> Nat x Nat) : Prop :=
  (Forall i, (I i).1 + 1 < (I i).2) /\
  (Forall i j, i != j -> (I i).2 < (I j).1 \/ (I j).2 < (I i).1)

theorem msl_erdos289_a_m02_parent : Forall^f (k : Nat) in atTop, Exists I : Fin k -> Nat x Nat, fullOK k I /\ Sum i, runSum (I i).1 (I i).2 = (1 : Rat) := by sorry
