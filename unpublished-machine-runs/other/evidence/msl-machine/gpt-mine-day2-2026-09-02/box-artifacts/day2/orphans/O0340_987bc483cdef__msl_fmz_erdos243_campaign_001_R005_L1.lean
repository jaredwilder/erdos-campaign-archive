import Mathlib

set_option autoImplicit false



def a1 : Nat := 2
def a2 : Nat := 3
def a3 : Nat := 8
def a4 : Nat := 57
def a5 : Nat := 3193
def a6 : Nat := 10192057
-- sequence: Sylvester recurrence a_{n+1} = a_n*(a_n-1)+1, with ONE c=2 perturbation at n=2 (a3 = a2*(a2-1)+2)
theorem rec_normal1 : a2 = a1*(a1-1)+1 := by native_decide
theorem rec_perturb : a3 = a2*(a2-1)+2 := by native_decide
theorem rec_normal2 : a4 = a3*(a3-1)+1 := by native_decide
theorem rec_normal3 : a5 = a4*(a4-1)+1 := by native_decide
theorem rec_normal4 : a6 = a5*(a5-1)+1 := by native_decide
-- residual parameter t = r*(r-1) with r = a2: t*(t+1) = 6*7 = 42 = a2*(a2-1)*(a3-1)
theorem t_def : (42:Q) = a2*(a2-1)*((a2*(a2-1))+1) := by native_decide
-- exact finite telescoping identity with the signed residual term:
-- Sum_{n=1}^{5} 1/a_n = 1/(a1-1) - 1/(a6-1) - 1/(t*(t+1))
def LHS : Q := (1:Q)/2 + 1/3 + 1/8 + 1/57 + 1/3193
def RHS : Q := (1:Q)/1 - 1/10192057 - 1/42
theorem telescoping_fragment : LHS = RHS := by native_decide
-- residual size bound from the route thesis: eta = -1/42, |eta| = 1/42 < 1/(a2-1)^2 = 1/4
theorem residual_bound : (1:Q)/42 < 1/((a2:Q)-1)^2 := by native_decide

theorem msl_fmz_erdos243_campaign_001_R005_L1  : rec_normal1 ∧ rec_perturb ∧ rec_normal2 ∧ rec_normal3 ∧ rec_normal4 ∧ t_def ∧ telescoping_fragment ∧ residual_bound := by native_decide

-- axiom footprint
#print axioms a1
#print axioms a2
#print axioms a3
#print axioms a4
#print axioms a5
#print axioms a6
#print axioms rec_normal1
#print axioms rec_perturb
#print axioms rec_normal2
#print axioms rec_normal3
#print axioms rec_normal4
#print axioms t_def
#print axioms LHS
#print axioms RHS
#print axioms telescoping_fragment
#print axioms residual_bound
#print axioms msl_fmz_erdos243_campaign_001_R005_L1
