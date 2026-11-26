import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
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
import dep.Scheme.Bountiful
import dep.Scheme.Cell
import dep.Scheme.Row

universe u

namespace VaughtConjecture.CellScheme

open Finset

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β}

namespace Rows

variable {R : D.Rows.{u}} {X Y : Finset α × ℕ}

section LowerEmbedding

variable {φ : κ → ι} (hφ : E.IsLowerEmbedding D φ) {X' Y' : Finset β × ℕ} {h' : X' ≤ Y'}
  {h : X ≤ Y} (hX : φ '' E.below X' = D.below X) (hY : φ '' E.below Y' = D.below Y)

include hX hY

include hX hY in
/-- **Pullback of lifts along a lower embedding.**  If `φ` maps the cells below `X'` and `Y'`
onto the cells below `X` and `Y`, and the grade of `Y` is at most that of `Y'`, a capped lift of
`R` from `X` to `Y` pulls back to a capped lift of the pulled-back rows from `X'` to `Y'`. -/
theorem CappedLift.comap (hgrade : Y.2 ≤ Y'.2) (hl : R.CappedLift h) :
    (R.comap hφ).CappedLift h' := sorry

end LowerEmbedding

/-- **Pullback along an embedding of ground sets.**  The pullback of bountiful rows along the
inclusion of the cells visible through an embedding `f : β ↪ α` is bountiful. -/
theorem IsBountiful.comap (hR : R.IsBountiful) (f : β ↪ α) :
    (R.comap (IsLowerEmbedding.comap D f)).IsBountiful := sorry

/-- **Reindexing along an equivalence of cells.**  Bountifulness is preserved by reindexing the
cells along an equivalence. -/
theorem IsBountiful.reindex (hR : R.IsBountiful) (e : κ ≃ ι) :
    (R.comap (IsLowerEmbedding.reindex D e)).IsBountiful := sorry

end Rows

end VaughtConjecture.CellScheme
