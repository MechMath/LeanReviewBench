import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Label.Basic

universe u

namespace VaughtConjecture.Label

variable {α β δ : Ordinal.{u}} {x y c : Label.{u}}

/-- A label `c` is a *permitted cutoff* at stage `α` if `⊥ < c < α` (roadmap, `README.md`,
Layer 3).  Ordinal zero is a permitted cutoff at every positive stage. -/
def IsPermittedCutoff (α : Ordinal.{u}) (c : Label.{u}) : Prop := ⊥ < c ∧ c < α

/-- The permitted cutoffs at stage `ω` are countably many: they are the natural numbers. -/
instance countable_permittedCutoff :
    Countable {c : Label.{u} // IsPermittedCutoff Ordinal.omega0.{u} c} := sorry

end VaughtConjecture.Label
