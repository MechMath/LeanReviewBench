module

public import Mathlib.Data.FunLike.IsApply
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import dep.ToMathlib.MeasureTheory.MeasurableSpace.Option
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- Keep the mass at `some x` as mass at `x`, and discard the mass at `none`. -/
noncomputable def dropNone (μ : Measure (Option α)) : Measure α :=
  Measure.bind μ fun
    | none => 0
    | some x => Measure.dirac x

/-- Discarding the absent outcomes of a subprobability measure preserves its mass bound. -/
instance dropNone.instIsSubprobabilityMeasure (μ : Measure (Option α))
    [IsSubprobabilityMeasure μ] : IsSubprobabilityMeasure μ.dropNone := sorry

/-- Turn a subprobability measure into a measure on `Option α` by mapping successful outcomes
through `some` and assigning all missing mass to `none`.

The definition is meaningful for every measure. Its probability-measure law requires the
subprobability bound `μ univ ≤ 1`, supplied explicitly or inferred from
`IsSubprobabilityMeasure μ`. -/
noncomputable def withFailure (μ : Measure α) : Measure (Option α) :=
  Measure.map some μ + (1 - μ Set.univ) • Measure.dirac none

/-- Completing a subprobability measure with its missing mass is a probability measure. -/
instance withFailure.instIsProbabilityMeasure (μ : Measure α) [IsSubprobabilityMeasure μ] :
    IsProbabilityMeasure μ.withFailure := sorry

end MeasureTheory.Measure
