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
import dep.Extension.CoatomScheme
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

open Ordinal

namespace VaughtConjecture

open Finset

namespace Label

variable {k : ℕ} {x : Label.{u}}

/-- A label is **strongly coded** at grade `k`: it is bottom or an ordinal `ω · i + j` with
`j ≤ k + 1`.  This is the range of a row of grade `k` displayed in [Kni26, Lemma 2.5.13]; it is
not part of legality, and a construction that needs it imposes it on the rows it builds. -/
def IsStronglyCoded (k : ℕ) (x : Label.{u}) : Prop :=
  x = ⊥ ∨ ∃ i j : ℕ, j ≤ k + 1 ∧ x = ((ω * i + j : Ordinal.{u}) : Label.{u})

end Label

namespace CellScheme.Rows

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β} {φ : κ → ι}

/-- Rows are **coded**: every row value lies below `ω ^ 2`, that is, is bottom or an ordinal
`ω · i + j` [Kni26, Lemma 2.5.13, range normalization]. -/
def IsCoded (R : D.Rows.{u}) : Prop :=
  ∀ s t, R.row s t < ((ω ^ 2 : Ordinal.{u}) : Label.{u})

/-- The row of a cell `s` is **strongly coded**: its values are strongly coded at the grade of
`s` (finite part at most the grade plus one). -/
def IsStronglyCodedAt (R : D.Rows.{u}) (s : ι) : Prop :=
  ∀ t, Label.IsStronglyCoded (D.grade s) (R.row s t)

/-- Rows are **strongly coded**: the row of every cell is strongly coded at its grade. -/
def IsStronglyCoded (R : D.Rows.{u}) : Prop := ∀ s, R.IsStronglyCodedAt s

variable {R : D.Rows.{u}} {Q : E.Rows.{u}}

/-- Strongly coded rows are coded. -/
theorem IsStronglyCoded.isCoded (h : R.IsStronglyCoded) : R.IsCoded := sorry

/-- Coded rows pull back to coded rows along a lower embedding. -/
theorem IsCoded.comap (h : R.IsCoded) (hφ : E.IsLowerEmbedding D φ) : (R.comap hφ).IsCoded := sorry

/-- Strongly coded rows pull back to strongly coded rows along a lower embedding, which preserves
grades. -/
theorem IsStronglyCoded.comap (h : R.IsStronglyCoded) (hφ : E.IsLowerEmbedding D φ) :
    (R.comap hφ).IsStronglyCoded := sorry

end CellScheme.Rows

namespace Scheme

variable {n m : ℕ}

end Scheme

end VaughtConjecture
