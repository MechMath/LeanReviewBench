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

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n m : ℕ} {S T : Scheme.{u} n} {φ : Fin S.card → Fin T.card} (f : Fin m ↪ Fin n)

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ} {s t : StageType.{u} α n} {φ : Fin s.card → Fin t.card}

end StageType

namespace Scheme

variable {n : ℕ} (S : Scheme.{u} n) (j : ℕ)

variable {S j}

variable {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), j) ≤ S.toCellScheme.gradedIndex d}

end Scheme

namespace Scheme

variable {n : ℕ} {S : Scheme.{u} n} {r : Fin (S.card + 1) → Label.{u}}
  {h : ∀ d, ¬ ((univ : Finset (Fin n)), n) ≤ S.toCellScheme.gradedIndex d}

/-- A scheme on `n` points is **legal below the full grade**: every law of a legal scheme
(`Scheme.IsLegal`), with completeness only below the full grade `n`, and every cell of grade below
`n`.  Appending a cell of full scope and full grade makes it legal (`StageType.isLegal_addApex`).
-/
structure IsLegalBelowFullGrade (S : Scheme.{u} n) : Prop where
  /-- The scheme is well formed. -/
  isWellFormed : S.IsWellFormed
  /-- The rows are coded: every row value lies below `ω ^ 2`. -/
  isCoded : S.IsCoded
  /-- The rows are consistent [Kni26, Definition 2.5.12]. -/
  isConsistent : S.rows.IsConsistent
  /-- The rows are bountiful [Kni26, Definition 2.5.14], between any two graded faces. -/
  isBountiful : S.rows.IsBountiful
  /-- Every cell has grade below `n`. -/
  grade_lt (d : Fin S.card) : S.toCellScheme.grade d < n
  /-- Every graded face of grade below `n` is the graded index of a cell: completeness
  [Kni26, Definition 2.5.15] below the full grade. -/
  exists_gradedIndex_eq :
    ∀ X ∈ S.toCellScheme.gradedFaces, X.2 < n → ∃ d, S.toCellScheme.gradedIndex d = X

end Scheme

namespace StageType

variable {α : Ordinal.{u}} {n m : ℕ} {t : StageType.{u} α n}

variable (ht : t.IsLegalBelowFullGrade)

variable (hn : 0 < n)

end StageType

end VaughtConjecture
