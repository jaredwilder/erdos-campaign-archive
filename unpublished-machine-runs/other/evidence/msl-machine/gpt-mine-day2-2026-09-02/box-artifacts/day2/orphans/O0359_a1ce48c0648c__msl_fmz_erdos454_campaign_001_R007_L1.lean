import Mathlib

set_option autoImplicit false


-- Concrete Lean 4, core only, all total and decidable.

def charsEqAt (hay needle : List Char) (off : Nat) : Bool :=
  (hay.drop off).take needle.length == needle

def hasSubstr (needle hay : List Char) : Bool :=
  needle.isEmpty ||
  hay.length.foldr (fun _ acc => acc) false ||
  hayIdxLoop hay needle 0
某hayIdxLoop is replaced by the concrete total loop below:

def hayIdxLoop (hay needle : List Char) : Nat → Bool
  | i => if i > hay.length then false
         else charsEqAt hay needle i || hayIdxLoop hay needle (i+1)
termination_by i => hay.length + 1 - i

def hasSub (needle hay : List Char) : Bool :=
  needle.isEmpty || hayIdxLoop hay needle 0

-- The canonical statement text pinned under contract SHA 8fab17a4372ba50c:
def contractStatement : List Char :=
  "Let[f(n) = min_{i<n} (p_{n+i}+p_{n-i}),]where $p_k$ is the $k$th prime. Is it true that[limsup_n (f(n)-2p_n)=infty?]".data

def pinsAbsent : Bool :=
  !(hasSub "sign(".data contractStatement) &&
  !(hasSub "g_n".data contractStatement) &&
  !(hasSub "admissible-i".data contractStatement)

def check_L1 : Bool := pinsAbsent

theorem msl_fmz_erdos454_campaign_001_R007_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms charsEqAt
#print axioms hasSubstr
#print axioms hayIdxLoop
#print axioms hasSub
#print axioms contractStatement
#print axioms pinsAbsent
#print axioms check_L1
#print axioms msl_fmz_erdos454_campaign_001_R007_L1
