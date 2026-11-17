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
import dep.Extension.SourcePrefix
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

namespace VaughtConjecture.Label

open Finset Ordinal

variable {k : ℕ} {x y h : Label.{u}}

/-- The **grid point** `ω * b + k` of the block `b` at grade `k`. -/
noncomputable def gridPoint (k b : ℕ) : Label.{u} :=
  ((ω * (b : Ordinal.{u}) + (k : Ordinal.{u}) : Ordinal.{u}) : Label.{u})

variable {ι : Type*} [Fintype ι] {w w' a : ι → Label.{u}}

/-- The **value rank** of a label `x` for a labelling `w`: the number of distinct values of `w`,
other than bottom, that are at most `x`. -/
noncomputable def valueRank (w : ι → Label.{u}) (x : Label.{u}) : ℕ :=
  #{y ∈ univ.image w | y ≠ ⊥ ∧ y ≤ x}

/-- The **grid** at grade `k` with block bound `B`: bottom and the grid points of the blocks
`b ≤ B`.  Its largest member, `ω * B + k`, is its ceiling. -/
noncomputable def grid (k B : ℕ) : Finset Label.{u} :=
  insert ⊥ ((range (B + 1)).image (gridPoint k))

/-- The **agreement height** of two labellings in a finite set `G` of labels: the largest member
`x` of `G` at which they agree capped, `min (a d) x = min (b d) x` at every cell. -/
noncomputable def agreementHeight (G : Finset Label.{u}) (a b : ι → Label.{u}) : Label.{u} :=
  {x ∈ G | ∀ d, min (a d) x = min (b d) x}.sup id

variable {G : Finset Label.{u}} {b c : ι → Label.{u}}

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} [Fintype ι] {D : CellScheme ι α} {R : D.Rows.{u}} {k : ℕ}
  {w : ι → Label.{u}}

end VaughtConjecture.CellScheme.Rows
