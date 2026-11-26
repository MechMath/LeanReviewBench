import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
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
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Extension.Apex
import dep.Extension.Basic
import dep.Extension.CoatomAmalgam
import dep.Extension.CoatomScheme
import dep.Extension.Coding
import dep.Extension.CompletionBelowFullGrade
import dep.Extension.Merge
import dep.Extension.PinnedExtension
import dep.Extension.Seed
import dep.Extension.WitnessAlgebra
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

namespace VaughtConjecture.CellScheme

open Finset Label

variable {ι κ μ α : Type*} {D : CellScheme ι α} {E : CellScheme κ α} {F : CellScheme μ α}
  {φ : κ → ι} {ψ : μ → κ} {X Y Z Z' : Finset α × ℕ} {g : ℕ}

/-- A **source prefix** at the pair `Z`: a lower embedding `φ` of the source `E` into `D`, over
the same points, that keeps scopes and whose image contains every cell of `D` below `Z`.  Below
every pair `X ≤ Z` the cells of `D` are then the images of the cells of `E`. -/
structure IsSourcePrefix (E : CellScheme κ α) (D : CellScheme ι α) (φ : κ → ι)
    (Z : Finset α × ℕ) : Prop where
  /-- The cell map is a lower embedding. -/
  isLowerEmbedding : E.IsLowerEmbedding D φ
  /-- The cell map keeps scopes. -/
  scope_eq (t : κ) : D.scope (φ t) = E.scope t
  /-- Every cell of `D` below `Z` is the image of a cell of the source. -/
  mem_range (d : ι) : D.gradedIndex d ≤ Z → d ∈ Set.range φ

namespace IsSourcePrefix

variable (h : E.IsSourcePrefix D φ Z)

include h

/-- **Below a pair `X ≤ Z`, the cells are those of the source**: the cells of `D` below `X` are
exactly the images of the cells of the source below `X`. -/
theorem image_below (hX : X ≤ Z) : φ '' E.below X = D.below X := sorry

omit h in
/-- The identity is a source prefix at every pair. -/
protected theorem id (D : CellScheme ι α) (Z : Finset α × ℕ) : D.IsSourcePrefix D id Z := sorry

/-- **Composition**: a source prefix of a source prefix at `Z` is a source prefix at `Z`.  It is
used in the recursion on the grade to read the amalgam inside every scheme reached. -/
theorem comp (hψ : F.IsSourcePrefix E ψ Z) : F.IsSourcePrefix D (φ ∘ ψ) Z := sorry

/-- Below a pair `X ≤ Z`, the cells of the source and those of `D`, identified by the cell map. -/
noncomputable def belowEquiv (hX : X ≤ Z) : E.below X ≃ D.below X :=
  h.isLowerEmbedding.belowEquiv (h.image_below hX)

variable {R : D.Rows.{u}}

end IsSourcePrefix

end VaughtConjecture.CellScheme

namespace VaughtConjecture.CompletionBelowFullGrade

open Finset CellScheme

variable {α : Ordinal.{u}} {m : ℕ} {I : Seed.{u} α m} (F : CompletionBelowFullGrade I)
  {X Y : Finset (Fin (m + 2)) × ℕ}

end VaughtConjecture.CompletionBelowFullGrade
