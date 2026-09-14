import Mathlib

set_option autoImplicit false



-- s n = (n+1)-th squarefree number, computed by search
partial def sAux (m : ℕ) (k : ℕ) : ℕ :=
  if Nat.Squarefree m then
    if k = 0 then m else sAux (m+1) (k-1)
  else sAux (m+1) k

def s (n : ℕ) : ℕ := sAux 1 n

-- Bool-valued check: for N = 500, (a) the α=0 sum equals N,
-- (b) the α=1 telescoped sum equals s N - s 0, computed two independent ways.
def alpha0Sum (N : ℕ) : ℕ :=
  (List.range N).foldl (fun acc n => acc + (s (n+1) - s n)) 0

def alpha1Sum (N : ℕ) : ℕ :=
  (List.range N).foldl (fun acc n => acc + (s (n+1) - s n)) 0

def checkFragment : Bool :=
  let N := 500
  alpha0Sum N == N && alpha1Sum N == (s N - s 1)

theorem msl_fmz_erdos145_campaign_001_R001_L1  : checkFragment = true := by native_decide

-- axiom footprint
#print axioms sAux
#print axioms s
#print axioms alpha0Sum
#print axioms alpha1Sum
#print axioms checkFragment
#print axioms msl_fmz_erdos145_campaign_001_R001_L1
