import dep.LegacyMap
import dep.LogSum


/-!
# Kullback-Leibler divergence

Definition of Kullback-Leibler divergence and basic facts
-/

open MeasureTheory ProbabilityTheory Real

variable {Ω Ω' Ω'' Ω''' G: Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G] -- [MeasurableSingletonClass G]

variable {X : Ω → G} {Y : Ω' → G} -- [FiniteRange X] [FiniteRange Y]

-- one should add somewhere the hypotheses that μ, μ', and μ'' are all probability measures

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

/-- If `X'` is a copy of `X`, and `Y'` is a copy of `Y`, then `KL(X' ‖ Y') = KL(X ‖ Y)`. -/
lemma KL_div_eq_of_equiv (X' : Ω'' → G) (Y' : Ω''' → G)
    (hX : IdentDistrib X X' μ μ'') (hY : IdentDistrib Y Y' μ' μ''') :
    KL[X ; μ # Y ; μ'] = KL[X' ; μ'' # Y' ; μ'''] := by
  simp only [KL_div, PFRHistorical.map_eq_modern hX.aemeasurable_fst, PFRHistorical.map_eq_modern hX.aemeasurable_snd, PFRHistorical.map_eq_modern hY.aemeasurable_fst, PFRHistorical.map_eq_modern hY.aemeasurable_snd]
  congr with x
  congr
  · exact hX.map_eq
  · exact hX.map_eq
  · exact hY.map_eq

lemma KL_div_eq_sum [Fintype G] :
    KL[X ; μ # Y ; μ'] = ∑ x,
      (PFRHistorical.map X μ {x}).toReal * log ((PFRHistorical.map X μ {x}).toReal / (PFRHistorical.map Y μ' {x}).toReal) :=
  tsum_eq_sum (by simp)

/-- `KL(X ‖ Y) ≥ 0`.-/
lemma KL_div_nonneg [Fintype G] [MeasurableSingletonClass G] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (hX : Measurable X) (hY : Measurable Y)
    (habs : ∀ x, PFRHistorical.map Y μ' {x} = 0 → PFRHistorical.map X μ {x} = 0) : 0 ≤ KL[X ; μ # Y ; μ'] := by
  rw [KL_div_eq_sum]
  apply le_trans ?_ (sum_mul_log_div_leq (by simp) (by simp) ?_)
  · have : IsProbabilityMeasure (PFRHistorical.map Y μ') := PFRHistorical.map.instProbability Y μ' hY.aemeasurable
    have : IsProbabilityMeasure (PFRHistorical.map X μ) := PFRHistorical.map.instProbability X μ hX.aemeasurable
    simp
  · have : IsProbabilityMeasure (PFRHistorical.map Y μ') := PFRHistorical.map.instProbability Y μ' hY.aemeasurable
    intro i _ hi
    have hi := (ENNReal.toReal_eq_zero_iff _ |>.mp hi).resolve_right (measure_ne_top _ _)
    simp [habs i hi]

/-- `KL(X ‖ Y) = 0` if and only if `Y` is a copy of `X`. -/
lemma KL_div_eq_zero_iff_identDistrib [Fintype G] [MeasurableSingletonClass G]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hX : Measurable X) (hY : Measurable Y)
    (habs : ∀ x, PFRHistorical.map Y μ' {x} = 0 → PFRHistorical.map X μ {x} = 0) :
    KL[X ; μ # Y ; μ'] = 0 ↔ IdentDistrib X Y μ μ' := by
  have L (x : ℝ) : log (x / x) = 0 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · simp [hx]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [KL_div, PFRHistorical.map_eq_modern h.aemeasurable_fst, PFRHistorical.map_eq_modern h.aemeasurable_snd, h.map_eq, L]⟩
  let νY := PFRHistorical.map Y μ'
  have : IsProbabilityMeasure νY := PFRHistorical.map.instProbability Y μ' hY.aemeasurable
  let νX := PFRHistorical.map X μ
  have : IsProbabilityMeasure νX := PFRHistorical.map.instProbability X μ hX.aemeasurable
  obtain ⟨r, hr⟩ : ∃ (r : ℝ), ∀ x ∈ Finset.univ, (νX {x}).toReal = r * (νY {x}).toReal := by
    apply sum_mul_log_div_eq_iff (by simp) (by simp) (fun i _ hi ↦ ?_)
    · rw [KL_div_eq_sum] at h
      simpa using h
    · have hi := (ENNReal.toReal_eq_zero_iff _ |>.mp hi).resolve_right (measure_ne_top _ _)
      simpa [νX, νY, habs i hi]
  have r_eq : r = 1 := by
    have : r * ∑ x, (νY {x}).toReal = ∑ x, (νX {x}).toReal := by
      simp only [Finset.mul_sum, Finset.mem_univ, hr]
    simpa using this
  have : νX = νY := by
    apply Measure.ext_iff_singleton.mpr (fun x ↦ ?_)
    simpa [r_eq, ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)] using hr x (Finset.mem_univ _)
  exact ⟨hX.aemeasurable, hY.aemeasurable, by simpa [νX, νY, PFRHistorical.map_eq_modern hX.aemeasurable, PFRHistorical.map_eq_modern hY.aemeasurable] using this⟩

