
def foo : Nat := 1

def myNat : Nat := 42

namespace Baz

def qux : Nat := 2

end Baz

def quux : Nat := 3

def withPrio : Nat := 4

instance : Inhabited Bool := ⟨true⟩

theorem myLemma : True := sorry

/-- info: 53 -/
#guard_msgs in
#eval foo + myNat + Baz.qux + quux + withPrio + (if (default : Bool) then 1 else 0)

/-- info: myLemma : True -/
#guard_msgs in
#check myLemma

