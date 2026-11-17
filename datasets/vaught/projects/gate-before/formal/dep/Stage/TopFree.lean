import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Countable
import Mathlib.Order.InitialSeg
import Mathlib.Order.SupClosed
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

namespace VaughtConjecture.StageType

open Finset

variable {α : Ordinal.{u}} {n m : ℕ}

/-- A stage type is **top-free** when no cell carries the label `⊤`. -/
def IsTopFree (t : StageType.{u} α n) : Prop :=
  ∀ d, t.label d ≠ ⊤

variable {t : StageType.{u} α n}

/-- The restriction of a top-free stage type to a closed face is top-free: its labels are labels
of the stage type. -/
theorem IsTopFree.comap (ht : t.IsTopFree) {f : Fin m ↪ Fin n}
    (hf : univ.map f ∈ t.toCellScheme.faces) : (t.comap f hf).IsTopFree := sorry

/-- A reindexing of a top-free stage type is top-free. -/
theorem IsTopFree.reindex (ht : t.IsTopFree) (e : Fin m ≃ Fin n) : (t.reindex e).IsTopFree := sorry

end VaughtConjecture.StageType
