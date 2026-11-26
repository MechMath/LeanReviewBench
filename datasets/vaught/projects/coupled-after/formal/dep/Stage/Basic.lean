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
import dep.Stage.Scheme

universe u

namespace VaughtConjecture

open Finset Label

/-- A **stage type** at stage `α` on `n` points [Kni26, §3.1]: a scheme on `n` points with a label
section of its cells; the scheme is well formed with coded rows, the section is lawful, and every
label occurs at stage `α`. -/
structure StageType (α : Ordinal.{u}) (n : ℕ) extends Scheme.{u} n where
  /-- The label of each cell. -/
  label : Fin card → Label.{u}
  /-- The scheme is well formed. -/
  isWellFormed : toScheme.IsWellFormed
  /-- The rows are coded. -/
  isCoded : toScheme.IsCoded
  /-- The label section is lawful for the rows. -/
  isLawful : rows.IsLawful label
  /-- Every label occurs at stage `α`. -/
  atStage (d : Fin card) : AtStage α (label d)

namespace StageType

variable {α β γ : Ordinal.{u}} {n m k : ℕ}

/-- **Extensionality** for stage types: equal schemes and equal labels at cells with equal
positions. -/
@[ext (iff := false)] theorem ext {t u : StageType.{u} α n} (h : t.toScheme = u.toScheme)
    (hl : ∀ (i : Fin t.card) (j : Fin u.card), (i : ℕ) = j → t.label i = u.label j) : t = u := sorry

/-- The faces of a stage type form a plan on all of its points. -/
theorem isPlan (t : StageType.{u} α n) : Geometry.IsPlan univ t.toCellScheme.faces := sorry

variable (t : StageType.{u} α n) (f : Fin m ↪ Fin n) (g : Fin k ↪ Fin m)

/-- The **restriction** of a stage type to the closed face spanned by `f`: the restricted scheme
and the labels of the visible cells. -/
noncomputable def comap (hf : univ.map f ∈ t.toCellScheme.faces) : StageType.{u} α m where
  toScheme := t.toScheme.comap f
  label i := t.label (t.cellMap f i)
  isWellFormed := t.isWellFormed.comap f hf
  isCoded := t.isCoded.comap f
  isLawful := t.isLawful.comap (t.isLowerEmbedding_comap f)
  atStage _ := t.atStage _

/-- The **face map** along `f : Fin m ↪ Fin n` [Kni26, §3.1]: the restriction of a
stage type to the face spanned by `f` when that face is closed, and `none` when it is not. -/
noncomputable def restrictFace (f : Fin m ↪ Fin n) (t : StageType.{u} α n) :
    Option (StageType.{u} α m) :=
  if hf : univ.map f ∈ t.toCellScheme.faces then some (t.comap f hf) else none

/-- **Reindexing** a stage type along a bijection `e : Fin m ≃ Fin n` of points: the face map
along `e`, which is always defined. -/
noncomputable def reindex (e : Fin m ≃ Fin n) : StageType.{u} α m :=
  t.comap e.toEmbedding (sorry)

section OfIsLawful

variable (hα : Order.IsSuccPrelimit α) (S : Scheme.{u} n) (hw : S.IsWellFormed) (hc : S.IsCoded)
  (ρ : Fin S.card → Label.{u}) (hρ : S.rows.IsLawful ρ)

variable {S hw hc ρ hρ}

end OfIsLawful

end StageType

end VaughtConjecture
