module

-- Tests scope tracking with public section (module system syntax)
-- The public section is left unclosed, which is common in Mathlib
public section

def publicValue : Nat := 42

namespace Inner
def innerValue : Nat := 100
end Inner
