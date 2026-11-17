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
import dep.Scheme.Row

universe u

namespace VaughtConjecture.Label

variable {N i : ℕ} {a b c v x : Label.{u}} {g : ℕ → Label.{u}} {σ : Label.{u} → Label.{u}}

end VaughtConjecture.Label

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} {R : D.Rows.{u}} {G C : ι} {P Q : Set ι}
  {w q : ι → Label.{u}}

/-- How the row of the gate `G` reads a cell `e` below it, relative to the display `w`, the
private cap `C`, and the private cells `P`. -/
inductive GateReads (R : D.Rows.{u}) (G C : ι) (P : Set ι) (w : ι → Label.{u})
    (e : D.below (D.gradedIndex G)) : Prop
  /-- A bottom label, read as bottom. -/
  | bot (hwe : w e = ⊥) (hrow : R.row G e = ⊥)
  /-- A bottom label, read at most as a private cell labelled bottom. -/
  | botAnchor (z : D.below (D.gradedIndex G)) (hz : z.1 ∈ P) (hwz : w z = ⊥) (hwe : w e = ⊥)
      (hrow : R.row G e ≤ R.row G z)
  /-- A label `vr_N(w z, i)` of the anchor `z`, read as `vr_N` of the reading of `z`. -/
  | ref (z : D.below (D.gradedIndex G)) (hz : z.1 ∈ P) (i : ℕ) (hi : i ≤ D.grade G)
      (hwe : w e = visibilityReplace (D.grade G) i (w z))
      (hrow : R.row G e = visibilityReplace (D.grade G) i (R.row G z))
  /-- A label at least that of the private cap, read at least as a private cell labelled at
  least that of the private cap. -/
  | top (z : D.below (D.gradedIndex G)) (hz : z.1 ∈ P) (hzC : w C ≤ w z) (heC : w C ≤ w e)
      (hrow : R.row G z ≤ R.row G e)

/-- **Gate data**: the private cap `C` is a private cell, not bottom in the display `w`, of the
grade of the gate `G` with scope inside that of `G`; every donor cell lies below the gate, and the
row of the gate reads every donor cell outside the private cells.  Nothing is said about the
twins of the gate. -/
structure IsGate (R : D.Rows.{u}) (G C : ι) (P Q : Set ι) (w : ι → Label.{u}) : Prop where
  /-- The private cap is a private cell. -/
  cap_mem : C ∈ P
  /-- The scope of the private cap lies in that of the gate. -/
  scope_cap_subset : D.scope C ⊆ D.scope G
  /-- The private cap has the grade of the gate. -/
  grade_cap : D.grade C = D.grade G
  /-- The private cap is not bottom in the display. -/
  cap_ne_bot : w C ≠ ⊥
  /-- Every donor cell lies below the gate. -/
  le_gate : ∀ e ∈ Q, D.gradedIndex e ≤ D.gradedIndex G
  /-- The row of the gate reads every donor cell outside the private cells. -/
  reads : ∀ e (he : e ∈ Q), e ∉ P → GateReads R G C P w ⟨e, le_gate e he⟩

namespace IsLawful

end IsLawful

namespace IsGate

variable (hgate : R.IsGate G C P Q w) (hq : R.IsLawful q) (hlit : ∀ x ∈ P, q x = w x)
  (htwin : ∀ t, D.gradedIndex t = D.gradedIndex G → t ≠ G → q t = ⊥)

include hgate hq hlit htwin

end IsGate

end VaughtConjecture.CellScheme.Rows
