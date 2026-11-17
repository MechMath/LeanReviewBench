import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Label.Basic
import dep.Label.OrdinalVisibility

universe u

namespace VaughtConjecture.Label

open Ordinal

variable {α o : Ordinal.{u}} {K k k' i : ℕ} {x y c : Label.{u}}

/-- Visibility replacement of labels at threshold `k` with value `i` [Kni26, Definition 2.2.3]:
bottom and the formal top are fixed, and an ordinal label is replaced by
`Ordinal.visibilityReplace k i`. -/
noncomputable def visibilityReplace (k i : ℕ) : Label.{u} → Label.{u} :=
  WithBot.map (WithTop.map (Ordinal.visibilityReplace k i))

/-- A label is *self-visible* at threshold `k` if visibility replacement at threshold `k` with
value `k` fixes it: bottom, the formal top, or an ordinal whose finite part is at least `k`. -/
def IsSelfVisible (k : ℕ) (x : Label.{u}) : Prop := visibilityReplace k k x = x

section Block

variable {μ : Ordinal.{u}} {n : ℕ}

end Block

/-- The minimum of two self-visible labels is self-visible. -/
theorem IsSelfVisible.min (hx : IsSelfVisible k x) (hy : IsSelfVisible k y) :
    IsSelfVisible k (min x y) := sorry

/-- The maximum of two self-visible labels is self-visible. -/
theorem IsSelfVisible.max (hx : IsSelfVisible k x) (hy : IsSelfVisible k y) :
    IsSelfVisible k (max x y) := sorry

section

variable {β : Ordinal.{u}}

end

end VaughtConjecture.Label
