import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Countable
import Mathlib.Order.InitialSeg
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Extension.Basic
import dep.Extension.CoatomScheme
import dep.Extension.Merge
import dep.Geometry.ConvexGeometry
import dep.Geometry.Plan
import dep.Label.Basic
import dep.Label.Cap
import dep.Label.OrdinalVisibility
import dep.Label.Transform
import dep.Label.Visibility
import dep.Scheme.Bountiful
import dep.Scheme.Cell
import dep.Scheme.Row
import dep.Scheme.Transport
import dep.Stage.Basic
import dep.Stage.Countable
import dep.Stage.Legal
import dep.Stage.Scheme

universe u

namespace VaughtConjecture.Coatom

open Finset Label

variable {m : ℕ} {Sa Sb : Scheme.{u} (m + 1)} (h : Sa.comap (face m) = Sb.comap (face m))

variable (Sa Sb) in
/-- The number of cells of the amalgam. -/
noncomputable def amalgamCard : ℕ := Sa.card + (Sb.card - (Sa.comap (face m)).card)

/-- The cells of the amalgam, enumerated in the merged order. -/
noncomputable def amalgamEnum : Fin (amalgamCard Sa Sb) ≃o AmalgamCell h :=
  Fintype.orderIsoFinOfCardEq (AmalgamCell h) (Merge.card _ _)

/-- The **amalgamated scheme** of two coatom schemes, on `m + 2` points [Kni26, Definition 4.3.1]:
the amalgamated cell scheme with its cells enumerated in the merged order. -/
noncomputable def amalgam : Scheme.{u} (m + 2) where
  card := amalgamCard Sa Sb
  toCellScheme := (amalgamCellScheme h).reindex (amalgamEnum h).toEquiv
  rows := (amalgamRows h).comap
    (CellScheme.IsLowerEmbedding.reindex (amalgamCellScheme h) (amalgamEnum h).toEquiv)

section StageType

variable {α : Ordinal.{u}}

variable {ta tb : StageType.{u} α (m + 1)} {p : StageType.{u} α m}
  (hta : StageType.restrictFace (face m) ta = some p)
  (htb : StageType.restrictFace (face m) tb = some p)

end StageType

end VaughtConjecture.Coatom
