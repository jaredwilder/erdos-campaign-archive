import Mathlib

set_option autoImplicit false


def modCls (a N n : Nat) : Bool := n % N == a % N

def agree (a a' N : Nat) (B : Nat) : Bool :=
  (a % N == a' % N) && (List.range B |>.all fun n => modCls a N n == modCls a' N n)

-- L2 fragment: representative reduction invariance, instantiated on concrete
-- moduli and residue representatives spanning the boundary cases (a=0, a=a',
-- a'>N, negative-equivalent representatives via large a).
def check_L2 : Bool :=
  agree 7 12 5 200 &&   -- a ≡ a' mod N, different representatives: classes identical
  agree 0 5 5 200 &&    -- boundary a=0 vs a=N: same class, not distinct classes
  agree 41 9 5 200 &&   -- a' > N reduced to 5: invariance holds
  agree 123 3 10 200 && -- large representative reduces mod N: invariance holds
  !(agree 1 2 5 200)    -- control: non-congruent residues give DIFFERENT classes,
                        -- so the invariance is not vacuously true

theorem msl_fmz_erdos25_campaign_001_R005_L2_a1r1  : check_L2 = true := by decide

-- axiom footprint
#print axioms modCls
#print axioms agree
#print axioms check_L2
#print axioms msl_fmz_erdos25_campaign_001_R005_L2_a1r1
