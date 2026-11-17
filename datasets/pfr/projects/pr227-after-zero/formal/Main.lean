import Mathlib
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic
import dep.LegacyMap

open MeasureTheory ProbabilityTheory Real

variable {Ω Ω' Ω'' Ω''' G: Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G]

variable {X : Ω → G} {Y : Ω' → G}

/-- If `X, Y` are two `G`-valued random variables, the Kullback--Leibler divergence is defined as
  `KL(X ‖ Y) := ∑ₓ 𝐏(X = x) log (𝐏(X = x) / 𝐏(Y = x))`.

Note that due to Lean conventions with junk values, this definition only makes sense when
`X` is absolutely continuous wrt to `Y`, i.e., `∀ x, 𝐏(Y = x) = 0 → 𝐏(X = x) = 0`. Otherwise, the
divergence should be infinite, but since we use real numbers for ease of computations, this is
not a possible choice.
  -/
noncomputable def KL_div (X : Ω → G) (Y: Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  ∑' x, (PFRHistorical.map X μ {x}).toReal * log ((PFRHistorical.map X μ {x}).toReal / (PFRHistorical.map Y μ' {x}).toReal)

@[inherit_doc KL_div] notation3:max "KL[" X " ; " μ " # " Y " ; " μ' "]" => KL_div X Y μ μ'

@[inherit_doc KL_div] notation3:max "KL[" X " # " Y "]" => KL_div X Y volume volume

/-- `KL(X ‖ Y) = 0` if and only if `Y` is a copy of `X`. -/
lemma KL_div_eq_zero_iff_identDistrib [Fintype G] [MeasurableSingletonClass G]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hX : Measurable X) (hY : Measurable Y)
    (habs : ∀ x, PFRHistorical.map Y μ' {x} = 0 → PFRHistorical.map X μ {x} = 0) :
    KL[X ; μ # Y ; μ'] = 0 ↔ IdentDistrib X Y μ μ' := sorry
