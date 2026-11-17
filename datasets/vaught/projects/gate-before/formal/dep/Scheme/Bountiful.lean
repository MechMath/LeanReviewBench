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

namespace VaughtConjecture.CellScheme.Rows

open Label

variable {ι α : Type*} {D : CellScheme ι α} (R : D.Rows.{u}) {X Y : Finset α × ℕ}
  {c c' : Label.{u}} {q q' : D.below X → Label.{u}}

/-- The **cap ball** of `q` at the cap `c`: the labellings lawful below `X` whose capped
observation at `c` agrees with that of `q` at every cell below `X`. -/
def capBall (X : Finset α × ℕ) (c : Label.{u}) (q : D.below X → Label.{u}) :
    Set (D.below X → Label.{u}) :=
  {q' | R.IsLawfulBelow X q' ∧ ∀ d, min (q' d) c = min (q d) c}

/-- The rows **lift capped** from `X` to `Y ≥ X`: for every cap `c` self-visible at the grade of
`Y` and every `q` lawful below `Y`, restriction from the cells below `Y` to those below `X` maps
the cap ball of `q` at `c` onto the cap ball of the restriction of `q`. -/
def CappedLift (h : X ≤ Y) : Prop :=
  ∀ c : Label.{u}, IsSelfVisible Y.2 c → ∀ q : D.below Y → Label.{u}, R.IsLawfulBelow Y q →
    Set.SurjOn (fun q' ↦ q' ∘ Set.inclusion (D.below_mono h)) (R.capBall Y c q)
      (R.capBall X c (q ∘ Set.inclusion (D.below_mono h)))

/-- The rows are **bountiful** [Kni26, §2.5]: they lift capped between any two graded faces
`X ≤ Y`, that is, for every cap `c` self-visible at the grade of `Y` and every `q` lawful below
`Y`, restriction from the cells below `Y` to those below `X` maps the cap ball of `q` at `c` onto
the cap ball of the restriction of `q`.

The caps at which bountifulness is required are the labels self-visible at the target grade.  This
is a different set from the stage-permitted cutoffs `Label.IsPermittedCutoff` (e.g. the ordinal
`0` is a permitted cutoff at every positive stage but is not self-visible at any grade `≥ 1`); how
model-level cutoffs are matched with scheme-level caps is settled with the stage types. -/
def IsBountiful : Prop :=
  ∀ ⦃X Y : Finset α × ℕ⦄, X ∈ D.gradedFaces → Y ∈ D.gradedFaces → ∀ h : X ≤ Y, R.CappedLift h

section CappedLift

variable {R} {Z : Finset α × ℕ}

/-- **Composition of lifts**: capped lifts from `X` to `Y` and from `Y` to `Z` compose to a capped
lift from `X` to `Z`. -/
theorem CappedLift.trans {hXY : X ≤ Y} {hYZ : Y ≤ Z} (hl : R.CappedLift hXY)
    (hr : R.CappedLift hYZ) : R.CappedLift (hXY.trans hYZ) := sorry

end CappedLift

end Rows

end VaughtConjecture.CellScheme
