import Mathlib.SetTheory.Ordinal.Arithmetic

universe u

namespace Ordinal

variable {α o : Ordinal.{u}} {K k i : ℕ}

open Classical in
/-- Visibility replacement of an ordinal at threshold `k` with value `i` [Kni26, Definition
2.2.3]: the finite part `o % ω` is replaced by `i` if it is below `k`, and kept otherwise. -/
noncomputable def visibilityReplace (k i : ℕ) (o : Ordinal.{u}) : Ordinal.{u} :=
  ω * (o / ω) + if o % ω < k then (i : Ordinal.{u}) else o % ω

end Ordinal
