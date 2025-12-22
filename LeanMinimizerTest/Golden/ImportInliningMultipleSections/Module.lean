module

-- Tests scope tracking with multiple unclosed sections
-- @[expose] public section followed by noncomputable section
@[expose] public section

noncomputable section

def someValue : Nat := 42
