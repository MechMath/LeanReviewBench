module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Insert
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.UniformOn
public import dep.PFR.ForMathlib.Entropy.Kernel.Basic
public import dep.PFR.ForMathlib.Entropy.Measure
public import dep.PFR.ForMathlib.FiniteRange.Defs
public import dep.PFR.Mathlib.MeasureTheory.Measure.Prod
public import dep.PFR.Mathlib.Probability.Kernel.Composition.Comp
public import dep.PFR.Mathlib.Probability.Kernel.Disintegration

@[expose] public section

open Function MeasureTheory Real

open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}

/-- Mutual information of a kernel into a product space with respect to a measure. -/
noncomputable
def mutualInfo (κ : Kernel T (S × U)) (μ : Measure T) : ℝ :=
  Hk[fst κ, μ] + Hk[snd κ, μ] - Hk[κ, μ]

/-- Mutual information of a kernel into a product space with respect to a measure. -/
notation3:100 "Ik[" κ " , " μ "]" => Kernel.mutualInfo κ μ

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass U]

variable [MeasurableSingletonClass T]

variable [Countable S] [Countable T]

variable [Countable U]

end

section

variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]

instance IsZeroOrProbabilityMeasure.compProd
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) [IsZeroOrProbabilityMeasure μ] (κ : Kernel α β)
    [IsZeroOrMarkovKernel κ] : IsZeroOrProbabilityMeasure (μ ⊗ₘ κ) := sorry

end

end ProbabilityTheory.Kernel
