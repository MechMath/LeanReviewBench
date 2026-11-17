import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Insert
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Kernel.IndepFun
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.UniformOn
import Mathlib.Tactic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Finiteness
import Mathlib.Util.Notation3
import dep.LegacyMap
import dep.PFR.ForMathlib.Entropy.Kernel.Basic
import dep.PFR.ForMathlib.Entropy.Kernel.MutualInfo
import dep.PFR.ForMathlib.Entropy.Measure
import dep.PFR.ForMathlib.FiniteRange.Defs
import dep.PFR.ForMathlib.Pair
import dep.PFR.ForMathlib.Uniform
import dep.PFR.Mathlib.MeasureTheory.Constructions.Pi
import dep.PFR.Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import dep.PFR.Mathlib.MeasureTheory.Measure.Prod
import dep.PFR.Mathlib.Probability.IdentDistrib
import dep.PFR.Mathlib.Probability.Independence.Basic
import dep.PFR.Mathlib.Probability.Kernel.Composition.Comp
import dep.PFR.Mathlib.Probability.Kernel.Disintegration

open MeasureTheory ProbabilityTheory

namespace PFRHistorical

noncomputable def measureEntropy {S : Type*} [Fintype S] [MeasurableSpace S]
    (μ : Measure S) : ℝ :=
  ∑ s, (- (((μ Set.univ)⁻¹ • μ) {s}).toReal * Real.log (((μ Set.univ)⁻¹ • μ) {s}).toReal)

noncomputable def entropy {Ω S : Type*} [MeasurableSpace Ω] [Fintype S] [MeasurableSpace S]
    (X : Ω → S) (μ : Measure Ω) := measureEntropy (PFRHistorical.map X μ)

end PFRHistorical

variable {Ω G : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Fintype G]

lemma ent_of_diff_le (X : Ω → G) (Y : Ω → G) (Z : Ω → G)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : IndepFun ((fun ω => (X ω, Y ω))) Z μ) [IsProbabilityMeasure μ] :
    PFRHistorical.entropy (X - Y) μ ≤ PFRHistorical.entropy (X - Z) μ + PFRHistorical.entropy (Z - Y) μ - PFRHistorical.entropy (Z) μ := sorry
