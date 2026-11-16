import dep.PFR.ForMathlib.Entropy.RuzsaDist
import dep.LegacyMap
open MeasureTheory ProbabilityTheory
namespace PFRHistorical
noncomputable def measureEntropy {S : Type*} [Fintype S] [MeasurableSpace S]
    (μ : Measure S) : ℝ :=
  ∑ s, (- (((μ Set.univ)⁻¹ • μ) {s}).toReal * Real.log (((μ Set.univ)⁻¹ • μ) {s}).toReal)
noncomputable def entropy {Ω S : Type*} [MeasurableSpace Ω] [Fintype S] [MeasurableSpace S]
    (X : Ω → S) (μ : Measure Ω) := measureEntropy (PFRHistorical.map X μ)
theorem entropy_eq_modern {Ω S : Type*} [MeasurableSpace Ω] [Fintype S] [MeasurableSpace S]
    (X : Ω → S) (μ : Measure Ω) (hX : Measurable X) :
    entropy X μ = ProbabilityTheory.entropy X μ := by
  simp [entropy, measureEntropy, PFRHistorical.map_eq_modern hX.aemeasurable,
    ProbabilityTheory.entropy, ProbabilityTheory.measureEntropy, Real.negMulLog, Measure.real]
end PFRHistorical
variable {Ω G : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Fintype G]
lemma ent_of_diff_le (X : Ω → G) (Y : Ω → G) (Z : Ω → G)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : IndepFun ((fun ω => (X ω, Y ω))) Z μ) [IsProbabilityMeasure μ] :
    PFRHistorical.entropy (X - Y) μ ≤ PFRHistorical.entropy (X - Z) μ + PFRHistorical.entropy (Z - Y) μ - PFRHistorical.entropy (Z) μ := by
  simpa only [PFRHistorical.entropy_eq_modern _ μ (hX.sub hY),
    PFRHistorical.entropy_eq_modern _ μ (hX.sub hZ),
    PFRHistorical.entropy_eq_modern _ μ (hZ.sub hY),
    PFRHistorical.entropy_eq_modern _ μ hZ]
    using (ent_of_diff_le_modern X Y Z hX hY hZ h)
