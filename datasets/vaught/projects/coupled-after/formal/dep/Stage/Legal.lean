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
import dep.Stage.Scheme

universe u

namespace VaughtConjecture

open Finset Label

namespace Scheme

variable {n m : ℕ} (S : Scheme.{u} n) (f : Fin m ↪ Fin n)

/-- A scheme on `n` points is **legal**: it is well formed, and its rows are coded, consistent,
and bountiful, and it is complete; that is, it is a domain with a semantics as required for the
types of [Kni26, Definition 3.1.1].  The recoverability of `⟨B,j⟩`, `P↾B`, `D⟨B,j⟩`, and
`E⟨B,j⟩` from a cell in [Kni26, Definition 2.6.1] holds by representation (the rows are a field of
the scheme); `IsCoded` is only the range normalization of [Kni26, Lemma 2.5.13]. -/
structure IsLegal : Prop where
  /-- The scheme is well formed. -/
  isWellFormed : S.IsWellFormed
  /-- The rows are coded. -/
  isCoded : S.IsCoded
  /-- The rows are consistent. -/
  isConsistent : S.rows.IsConsistent
  /-- The rows are bountiful. -/
  isBountiful : S.rows.IsBountiful
  /-- Every graded face is the graded index of a cell. -/
  isComplete : S.toCellScheme.IsComplete

variable {S}

/-- **Restriction to a closed face** of a legal scheme is legal. -/
theorem IsLegal.comap (hS : S.IsLegal) (hf : univ.map f ∈ S.toCellScheme.faces) :
    (S.comap f).IsLegal := sorry

/-- **Reindexing** a legal scheme along a bijection of points gives a legal scheme. -/
theorem IsLegal.reindex (hS : S.IsLegal) (e : Fin m ≃ Fin n) :
    (S.comap e.toEmbedding).IsLegal := sorry

end Scheme

namespace StageType

variable {α β γ : Ordinal.{u}} {n m : ℕ} (t : StageType.{u} α n) (f : Fin m ↪ Fin n)

/-- A stage type is **legal** when its scheme is legal: its rows are consistent and bountiful and
its scheme is complete [Kni26, Definition 3.1.1].  A `StageType` alone is the unrestricted
structure. -/
def IsLegal : Prop := t.toScheme.IsLegal

variable {t}

/-- The restriction of a legal stage type to a closed face is legal. -/
theorem IsLegal.comap (ht : t.IsLegal) (hf : univ.map f ∈ t.toCellScheme.faces) :
    (t.comap f hf).IsLegal := sorry

/-- Reindexing a legal stage type along a bijection of points gives a legal stage type. -/
theorem IsLegal.reindex (ht : t.IsLegal) (e : Fin m ≃ Fin n) : (t.reindex e).IsLegal := sorry

variable (t)

end StageType

namespace Scheme

variable {n m : ℕ} {S : Scheme.{u} n} {f : Fin m ↪ Fin n}

end Scheme

namespace StageType

variable {α β : Ordinal.{u}} {n m : ℕ}

section Extend

variable {f : Fin m ↪ Fin n} {S : Scheme.{u} n} {p : StageType.{u} α m}

end Extend

section Lift

variable {f : Fin m ↪ Fin n} {p : StageType.{u} α m} {q' : StageType.{u} β n} {c : Label.{u}}

end Lift

end StageType

end VaughtConjecture
