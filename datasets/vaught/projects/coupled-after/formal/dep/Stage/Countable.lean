import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Countable
import Mathlib.Order.InitialSeg
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Geometry.ConvexGeometry
import dep.Geometry.Plan
import dep.Label.Basic
import dep.Label.OrdinalVisibility
import dep.Label.Transform
import dep.Label.Visibility
import dep.Scheme.Cell
import dep.Scheme.Row
import dep.Stage.Basic
import dep.Stage.Scheme

universe u

namespace VaughtConjecture

open Cardinal Ordinal

namespace StageType

variable {α : Ordinal.{u}}

end StageType

/-- The ordinals below `ω` form a countable type. -/
instance countable_Iio_omega0_coe : Countable (Set.Iio (ω : Ordinal.{u})) := sorry

end VaughtConjecture
