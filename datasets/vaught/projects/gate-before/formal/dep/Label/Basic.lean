import Mathlib.SetTheory.Ordinal.Arithmetic

universe u

namespace VaughtConjecture

/-- The labels: the bottom label `⊥`, the ordinals, and the formal top `⊤`, ordered with `⊥`
least and `⊤` greatest.  The formal top is not an ordinal. -/
abbrev Label : Type (u + 1) := WithBot (WithTop Ordinal.{u})

namespace Label

variable {α β o : Ordinal.{u}} {x y : Label.{u}}

/-- The label `x` *occurs at stage* `α`: it is below the ordinal `α` (bottom included) or it is
the formal top.  These are the labels `{-∞} ∪ α ∪ {∞}` of a stage type at stage `α`. -/
def AtStage (α : Ordinal.{u}) (x : Label.{u}) : Prop := x < α ∨ x = ⊤

section Countability

open Cardinal Ordinal

end Countability

end Label

end VaughtConjecture
