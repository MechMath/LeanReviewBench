module

public import Mathlib.Tactic.Attr.Register

public section

/-- Rewrite rules bringing an event computation into the normal form of `Pr{…}[…]`. -/
register_simp_attr prEvent_norm
