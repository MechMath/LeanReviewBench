import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Countable
import Mathlib.Order.InitialSeg
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Extension.Basic
import dep.Extension.Merge
import dep.Geometry.ConvexGeometry
import dep.Geometry.Plan
import dep.Label.Basic
import dep.Label.OrdinalVisibility
import dep.Label.Transform
import dep.Label.Visibility
import dep.Scheme.Bountiful
import dep.Scheme.Cell
import dep.Scheme.Row
import dep.Scheme.Transport
import dep.Stage.Scheme

universe u

namespace VaughtConjecture

open Finset

/-- A plan pushed forward along an embedding of ground types is a plan on the image. -/
theorem Geometry.IsPlan.map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β)
    {A : Finset α} {P : Finset (Finset α)} (hP : IsPlan A P) :
    IsPlan (A.map f) (P.map (mapEmbedding f).toEmbedding) := sorry

namespace Scheme

variable {n : ℕ} {S T : Scheme.{u} n}

end Scheme

/-- The image under a lower embedding of the cells below a cell is the set of cells below its
image. -/
theorem CellScheme.IsLowerEmbedding.image_below_gradedIndex {ι κ α β : Type*}
    {E : CellScheme κ β} {D : CellScheme ι α} {φ : κ → ι} (hφ : E.IsLowerEmbedding D φ)
    (s : κ) : φ '' E.below (E.gradedIndex s) = D.below (D.gradedIndex (φ s)) := sorry

namespace Coatom

variable {m : ℕ}

/-- The common face of the two coatoms: `Fin m` in `Fin (m + 1)`. -/
abbrev face (m : ℕ) : Fin m ↪ Fin (m + 1) := Fin.castSuccEmb

/-- The coatom of `Fin (m + 2)` omitting the last point. -/
abbrev left (m : ℕ) : Fin (m + 1) ↪ Fin (m + 2) := Fin.castSuccEmb

/-- The coatom of `Fin (m + 2)` omitting the point `m`. -/
abbrev right (m : ℕ) : Fin (m + 1) ↪ Fin (m + 2) := extendByLast (face m)

section Overlap

variable {Sa Sb : Scheme.{u} (m + 1)} (h : Sa.comap (face m) = Sb.comap (face m))

/-- The cells of `Sb` on the common face, in the order of the corresponding cells of `Sa`. -/
noncomputable def overlap : Fin (Sa.comap (face m)).card ↪o Fin Sb.card :=
  (Fin.castOrderIso (congrArg Scheme.card h)).toOrderEmbedding.trans (Sb.cellMap (face m))

end Overlap

section Amalgam

variable {Sa Sb : Scheme.{u} (m + 1)} (h : Sa.comap (face m) = Sb.comap (face m))

/-- The cells of the amalgam: the cells of `Sa`, and the cells of `Sb` outside the common face,
merged so that both orders are retained. -/
abbrev AmalgamCell := Merge (Sa.cellMap (face m)) (overlap h)

/-- The scope of a cell of the amalgam: the scope of the given cell, moved to `Fin (m + 2)`. -/
def amalgamScope : AmalgamCell h → Finset (Fin (m + 2))
  | .inl i => (Sa.toCellScheme.scope i).map (left m)
  | .inr j _ => (Sb.toCellScheme.scope j).map (right m)

/-- The grade of a cell of the amalgam: the grade of the given cell. -/
def amalgamGrade : AmalgamCell h → ℕ
  | .inl i => Sa.toCellScheme.grade i
  | .inr j _ => Sb.toCellScheme.grade j

variable (Sa Sb) in
/-- The faces of the amalgam: the ground set, and the faces of `Sa` and of `Sb` moved to
`Fin (m + 2)`. -/
def amalgamFaces : Finset (Finset (Fin (m + 2))) :=
  insert univ (Sa.toCellScheme.faces.map (mapEmbedding (left m)).toEmbedding ∪
    Sb.toCellScheme.faces.map (mapEmbedding (right m)).toEmbedding)

/-- The **amalgamated cell scheme** of two coatom schemes [Kni26, Definition 4.3.1]. -/
def amalgamCellScheme : CellScheme (AmalgamCell h) (Fin (m + 2)) where
  ground := univ
  faces := amalgamFaces Sa Sb
  scope := amalgamScope h
  grade := amalgamGrade h

/-- **The cells of `Sa` in the amalgam** form a lower embedding. -/
theorem isLowerEmbedding_left :
    Sa.toCellScheme.IsLowerEmbedding (amalgamCellScheme h) Merge.inl := sorry

/-- **The cells of `Sb` in the amalgam** form a lower embedding. -/
theorem isLowerEmbedding_right :
    Sb.toCellScheme.IsLowerEmbedding (amalgamCellScheme h) (Merge.rightFun _ (overlap h)) := sorry

/-- The cells below a cell of `Sb` outside the common face. -/
theorem image_right_below_inr (j : Fin Sb.card) (hj : j ∉ Set.range (overlap h)) :
    Merge.rightFun _ (overlap h) '' Sb.toCellScheme.below (Sb.toCellScheme.gradedIndex j) =
      (amalgamCellScheme h).below ((amalgamCellScheme h).gradedIndex (.inr j hj)) := sorry

/-- The **rows of the amalgam**: the rows of the given cells. -/
noncomputable def amalgamRows : (amalgamCellScheme h).Rows.{u} where
  row
    | .inl i => Sa.rows.row i ∘ ((isLowerEmbedding_left h).belowEquiv
        ((isLowerEmbedding_left h).image_below_gradedIndex i)).symm
    | .inr j hj => Sb.rows.row j ∘ ((isLowerEmbedding_right h).belowEquiv
        (image_right_below_inr h j hj)).symm

end Amalgam

end Coatom

end VaughtConjecture
