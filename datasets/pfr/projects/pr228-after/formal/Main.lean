import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.UniformOn
import Mathlib.Tactic
import dep.LegacyMap

open MeasureTheory ProbabilityTheory Real

open scoped Pointwise ENNReal

universe uG

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

variable {G : Type uG} [MeasurableSpace G]

noncomputable def KLDiv (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  ∑' x, (PFRHistorical.map X μ {x}).toReal * log ((PFRHistorical.map X μ {x}).toReal / (PFRHistorical.map Y μ' {x}).toReal)

notation3:max "KL[" X " ; " μ " # " Y " ; " μ' "]" => KLDiv X Y μ μ'

notation3:max "KL[" X " # " Y "]" => KLDiv X Y volume volume

variable [AddCommGroup G] [Fintype G] [DiscreteMeasurableSpace G]

noncomputable def rhoMinusSet {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : Set ℝ :=
  {x : ℝ | ∃ (μ : Measure G), IsProbabilityMeasure μ ∧
    (∀ y, PFRHistorical.map (Prod.fst + Prod.snd) (μ.prod (uniformOn A)) {y} = 0 → PFRHistorical.map X volume {y} = 0) ∧
    x = KL[X ; ℙ # Prod.fst + Prod.snd ; μ.prod (uniformOn A)]}

noncomputable def rhoMinus {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : ℝ :=
  sInf (rhoMinusSet X A)
