import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.InitialSeg
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Geometry.ConvexGeometry
import dep.Geometry.Plan
import dep.Label.Basic
import dep.Label.OrdinalVisibility
import dep.Label.Transform
import dep.Label.Visibility
import dep.Realization.Basic
import dep.Scheme.Cell
import dep.Scheme.Row
import dep.Stage.Basic
import dep.Stage.Scheme

universe u v

namespace VaughtConjecture

open Finset Geometry

namespace Realization

variable {α : Ordinal.{u}} {M : Type v} {m n : ℕ} {R : Realization.{u, v} α M}
  {F G S : Finset M}

namespace Occurrence

variable (x : R.Occurrence)

/-- The **support** of an occurrence: the points of its tuple. -/
def support : Finset M := univ.map x.tuple

end Occurrence

section Directed

/-- Occurrences are preordered by inclusion of supports. -/
instance : Preorder R.Occurrence :=
  Preorder.lift Occurrence.support

end Directed

namespace Occurrence

variable {x : R.Occurrence}

end Occurrence

end Realization

end VaughtConjecture
