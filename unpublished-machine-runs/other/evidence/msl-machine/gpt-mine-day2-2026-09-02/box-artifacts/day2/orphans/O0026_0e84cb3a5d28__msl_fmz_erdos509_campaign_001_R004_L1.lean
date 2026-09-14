import Mathlib

set_option autoImplicit false


-- Pure Lean 4 core. Int arithmetic only; everything decidable.

/-- Axis-aligned square with vertices (±1/2 scaled by 2) inside unit disc scaled by 2: points (±1, ±1) in |z| ≤ 2, i.e. |z|² = 2 < 4. -/
structure Pt where
  x : Int
  y : Int

def p1 : Pt := ⟨1, 1⟩
def p2 : Pt := ⟨1, -1⟩
def p3 : Pt := ⟨-1, -1⟩
def p4 : Pt := ⟨-1, 1⟩

/-- Vertex lies strictly inside the disc of radius 2 (unit disc scaled ×2): |z|² < 4. -/
def inside2 (p : Pt) : Bool := p.x * p.x + p.y * p.y < 4

/-- Side length of square = 2 (scaled ×2 from 1); area = 4 in scaled units > 0. -/
def areaPos : Bool := (2 * 2 > 0 : Bool)

def distinct : Bool :=
  p1 ≠ p2 && p1 ≠ p3 && p1 ≠ p4 && p2 ≠ p3 && p2 ≠ p4 && p3 ≠ p4

def check_L1_core : Bool :=
  inside2 p1 && inside2 p2 && inside2 p3 && inside2 p4 && distinct && areaPos

theorem msl_fmz_erdos509_campaign_001_R004_L1  : check_L1_core = true := by decide

-- axiom footprint
#print axioms p1
#print axioms p2
#print axioms p3
#print axioms p4
#print axioms inside2
#print axioms areaPos
#print axioms distinct
#print axioms check_L1_core
#print axioms msl_fmz_erdos509_campaign_001_R004_L1
