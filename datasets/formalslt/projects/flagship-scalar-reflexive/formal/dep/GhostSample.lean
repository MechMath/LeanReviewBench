import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Ring
import dep.Risk

namespace FormalSLT.GhostSample

open MeasureTheory

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

variable {Z : Type*} [MeasurableSpace Z]

/-- The iid product measure `μ^n` on `Fin n → Z`. Each coordinate is an
independent draw from `μ`. -/
noncomputable def piMeasure (μ : Measure Z) (n : ℕ) : Measure (Fin n → Z) :=
  Measure.pi (fun _ : Fin n => μ)

instance instIsProbabilityMeasurePi
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (piMeasure μ n) := sorry

end FormalSLT.GhostSample
