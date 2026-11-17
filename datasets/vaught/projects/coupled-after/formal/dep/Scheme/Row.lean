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
import dep.Scheme.Cell

universe u

namespace VaughtConjecture.CellScheme

open Label

variable {ι κ α β : Type*} {D : CellScheme ι α} {E : CellScheme κ β}

/-- The **semantic rows** of a cell scheme [Kni26, §2.5]: for every cell `s`, a labelling `row s`
of the cells below `s`.  The rows are data separate from the scheme; the bundle of a scheme with
its rows belongs to the stage types. -/
@[ext]
structure Rows (D : CellScheme ι α) where
  /-- The semantic row of a cell: a labelling of the cells below it. -/
  row (s : ι) : D.below (D.gradedIndex s) → Label.{u}

namespace Rows

variable (R : D.Rows) {φ : κ → ι}

/-- The pullback of rows along a lower embedding `φ` of `E` into `D`: the row of `s` at `t` is
the row of `φ s` at `φ t`. -/
def comap (hφ : E.IsLowerEmbedding D φ) : E.Rows where
  row s t := R.row (φ s) ⟨φ t, (hφ.le_iff t s).mpr t.2⟩

/-- A labelling `p` of the cells is a **lawful section** of the rows `R` [Kni26, §2.5]: it
satisfies the order, locality, and availability laws. -/
structure IsLawful (p : ι → Label.{u}) : Prop where
  /-- Order: the label of every cell is self-visible at the grade of the cell. -/
  orderly (d : ι) : IsSelfVisible (D.grade d) (p d)
  /-- Locality: the row of every cell `s` transforms, over the grades of the cells below `s`, to
  the labelling `d ↦ min (p d) (p s)` of the cells below `s`. -/
  locality (s : ι) : TransformsTo (fun d : D.below (D.gradedIndex s) ↦ D.grade d) (R.row s)
    (fun d ↦ min (p d) (p s))
  /-- Availability: if the scope of `s` lies in the scope of `t` and their grades agree, then
  some cell with the graded index of `t` has a label at least that of `s`. -/
  availability (s t : ι) : D.scope s ⊆ D.scope t → D.grade s = D.grade t →
    ∃ u, D.gradedIndex u = D.gradedIndex t ∧ p s ≤ p u

/-- A labelling `r` of the cells below `X` is *lawful below `X`*: it is a lawful section of the
rows restricted to the scheme `D⟨X⟩` of cells below `X`. -/
def IsLawfulBelow (X : Finset α × ℕ) (r : D.below X → Label.{u}) : Prop :=
  (R.comap (IsLowerEmbedding.subtypeVal_below D X)).IsLawful r

/-- The rows are **consistent** [Kni26, §2.5]: the row of every cell `s` is lawful
below the graded index of `s`. -/
def IsConsistent : Prop := ∀ s, R.IsLawfulBelow (D.gradedIndex s) (R.row s)

variable {R}

namespace IsLawful

variable {p : ι → Label.{u}}

include E in
/-- **Pullback of lawful sections**: along a lower embedding `φ`, a lawful section `p` of `R`
pulls back to the lawful section `p ∘ φ` of the pulled-back rows. -/
theorem comap (h : R.IsLawful p) (hφ : E.IsLowerEmbedding D φ) :
    (R.comap hφ).IsLawful (p ∘ φ) := sorry

end IsLawful

namespace IsLawfulBelow

variable {X Y : Finset α × ℕ}

include D in
/-- A labelling lawful below a pair lying above every cell is a lawful section. -/
theorem isLawful {r : D.below X → Label.{u}} (h : R.IsLawfulBelow X r)
    (hX : ∀ d, d ∈ D.below X) : R.IsLawful fun d ↦ r ⟨d, hX d⟩ := sorry

end IsLawfulBelow

namespace IsConsistent

/-- Consistency pulls back along lower embeddings. -/
theorem comap (hR : R.IsConsistent) (hφ : E.IsLowerEmbedding D φ) : (R.comap hφ).IsConsistent := sorry

end IsConsistent

variable (D) in
/-- The **bottom** rows: every row is constantly bottom [Kni26, §4.2]. -/
def bot : D.Rows.{u} := ⟨fun _ _ ↦ ⊥⟩

end Rows

end VaughtConjecture.CellScheme
