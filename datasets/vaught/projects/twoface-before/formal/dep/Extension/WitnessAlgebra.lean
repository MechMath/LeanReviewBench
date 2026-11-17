import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Label.Basic
import dep.Label.OrdinalVisibility
import dep.Label.Transform
import dep.Label.Visibility

universe u

namespace VaughtConjecture.Label

open Ordinal

section Blocks

variable {a b x y : Ordinal.{u}}

end Blocks

variable {D : Type*} {grade : D → ℕ} {g : ℕ → Label.{u}} {σ τ ν f : Label.{u} → Label.{u}}
  {m K k i : ℕ} {x c : Label.{u}}

/-- A label is **short** at grade `m`: it is bottom, the formal top, or an ordinal whose finite
part is at most `m`.  An owner is short when every entry of its row is short at its grade, and
the section theorem (`CellScheme.Rows.IsLawful.map_of_isShort_or`) needs no other condition at
such an owner.  Shortness of a row is not a consequence of the normal form: the normal forms of
`VaughtConjecture.Extension.NormalForm` have finite parts up to `K + 1`, so they are strongly
coded at `K` but not short at `K`.  Shortness of a new row of full scope is a property of the
construction of that row. -/
def IsShort (m : ℕ) (x : Label.{u}) : Prop := ∀ o : Ordinal.{u}, (o : Label.{u}) = x → o % ω ≤ m

end VaughtConjecture.Label
