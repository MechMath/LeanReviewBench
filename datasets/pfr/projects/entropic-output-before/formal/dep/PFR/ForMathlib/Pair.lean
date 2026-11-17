module

public import Mathlib.Tactic.Basic
public import Mathlib.Util.Notation3

public section

/-- The pair of two random variables -/
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)

@[inherit_doc prod] notation3:100 "⟨" X ", " Y "⟩" => prod X Y
