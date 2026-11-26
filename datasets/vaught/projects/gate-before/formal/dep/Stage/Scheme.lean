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

universe u

namespace VaughtConjecture

open Finset

/-- A **scheme on `n` points**: a cell scheme on the ground type `Fin n` with the cells
`Fin card`, in their order, together with its semantic rows.  This is raw data; the laws are
`Scheme.IsWellFormed` and `Scheme.IsCoded`. -/
structure Scheme (n : ℕ) : Type (u + 1) where
  /-- The number of cells. -/
  card : ℕ
  /-- The cell scheme: ground set, faces, and the scope and grade of each cell. -/
  toCellScheme : CellScheme (Fin card) (Fin n)
  /-- The semantic rows. -/
  rows : toCellScheme.Rows.{u}

namespace Scheme

variable {n m k : ℕ} (S : Scheme.{u} n)

/-- **Extensionality** for schemes: equal numbers of cells, equal ground sets and faces, and equal
scopes, grades, and rows at cells with equal positions. -/
@[ext (iff := false)] theorem ext {S T : Scheme.{u} n} (hcard : S.card = T.card)
    (hground : S.toCellScheme.ground = T.toCellScheme.ground)
    (hfaces : S.toCellScheme.faces = T.toCellScheme.faces)
    (hscope : ∀ (i : Fin S.card) (j : Fin T.card), (i : ℕ) = j →
      S.toCellScheme.scope i = T.toCellScheme.scope j)
    (hgrade : ∀ (i : Fin S.card) (j : Fin T.card), (i : ℕ) = j →
      S.toCellScheme.grade i = T.toCellScheme.grade j)
    (hrow : ∀ (s : Fin S.card) (s' : Fin T.card)
      (t : S.toCellScheme.below (S.toCellScheme.gradedIndex s))
      (t' : T.toCellScheme.below (T.toCellScheme.gradedIndex s')),
      (s : ℕ) = s' → (t.1 : ℕ) = t'.1 → S.rows.row s t = T.rows.row s' t') :
    S = T := sorry

variable (f : Fin m ↪ Fin n) (g : Fin k ↪ Fin m)

/-- The cells of `S` **visible through** `f`: those whose scope lies in the range of `f`. -/
def visibleCells : Finset (Fin S.card) := {d | S.toCellScheme.scope d ⊆ univ.map f}

variable {S f} in
/-- A cell is visible through `f` exactly when its scope lies in the range of `f`. -/
@[simp] theorem mem_visibleCells {d : Fin S.card} :
    d ∈ S.visibleCells f ↔ (S.toCellScheme.scope d : Set (Fin n)) ⊆ Set.range f := sorry

/-- The enumeration in increasing order of the cells visible through `f`, as an equivalence onto
the visible cells. -/
noncomputable def cellEquiv : Fin #(S.visibleCells f) ≃ S.toCellScheme.visible (Set.range f) :=
  ((S.visibleCells f).orderIsoOfFin rfl).toEquiv.trans
    (Equiv.subtypeEquivRight fun _ ↦ mem_visibleCells)

/-- The **restriction** of a scheme along `f : Fin m ↪ Fin n`: the pullback of the cell scheme
along `f` on the visible cells, enumerated in increasing order, with the rows of those cells. -/
noncomputable def comap : Scheme.{u} m where
  card := #(S.visibleCells f)
  toCellScheme := (S.toCellScheme.comap f).reindex (S.cellEquiv f)
  rows := S.rows.comap ((CellScheme.IsLowerEmbedding.comap _ f).comp
    (CellScheme.IsLowerEmbedding.reindex _ (S.cellEquiv f)))

/-- The **cell map** of the restriction along `f`: the visible cells of `S` in increasing
order. -/
noncomputable def cellMap : Fin (S.comap f).card ↪o Fin S.card :=
  (S.visibleCells f).orderEmbOfFin rfl

/-- The cell map is a lower embedding of the restriction into the scheme. -/
theorem isLowerEmbedding_comap :
    (S.comap f).toCellScheme.IsLowerEmbedding S.toCellScheme (S.cellMap f) := sorry

/-- The laws of a scheme on `n` points: the ground set is all of `Fin n`, and the cell scheme is
well formed (its faces form a plan and every cell has a graded face as graded index). -/
structure IsWellFormed : Prop where
  /-- The ground set is all of `Fin n`. -/
  ground_eq : S.toCellScheme.ground = univ
  /-- The cell scheme is well formed. -/
  isWellFormed : S.toCellScheme.IsWellFormed

/-- The rows of a scheme are **coded**: every row value is bottom or an ordinal `ω · i + j`
(`i j : ℕ`), that is, lies below `ω ^ 2` [Kni26, §2.5].  The bound `j ≤ k + 1` at a row
of grade `k` is not part of this law. -/
def IsCoded : Prop :=
  ∀ s t, S.rows.row s t < ((Ordinal.omega0 ^ 2 : Ordinal.{u}) : Label.{u})

namespace IsWellFormed

variable {S} (hS : S.IsWellFormed)

include hS

/-- The faces of a well-formed scheme form a plan on all of its points. -/
theorem isPlan : Geometry.IsPlan univ S.toCellScheme.faces := sorry

/-- **Restriction to a closed face** of a well-formed scheme is well formed. -/
theorem comap (hf : univ.map f ∈ S.toCellScheme.faces) : (S.comap f).IsWellFormed := sorry

end IsWellFormed

/-- The restriction of a scheme with coded rows has coded rows. -/
theorem IsCoded.comap {S : Scheme.{u} n} (hS : S.IsCoded) : (S.comap f).IsCoded := sorry

end Scheme

end VaughtConjecture
