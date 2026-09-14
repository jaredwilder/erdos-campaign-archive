namespace SelfA
def f (n : Nat) : Nat := n + 1
def k : Nat := 1
def wide (a b c : Nat) : Nat := a
end SelfA
namespace SelfB
def f (n : Nat) : Nat := n + 1
def k : Nat := 2
end SelfB
namespace InstanceCheck
open SelfA
theorem t : @SelfA.f = @SelfB.f := by rfl
end InstanceCheck
#print axioms InstanceCheck.t
