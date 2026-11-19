import dep.DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



variable (I M) in

def chartAtlasPOU [T2Space M] [SigmaCompactSpace M] :
    SmoothPartitionOfUnity M I M univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose

variable (I M) in

lemma chartAtlasPOU_isSubordinate [T2Space M] [SigmaCompactSpace M] :
    (chartAtlasPOU I M).IsSubordinate (fun x : M => (chartAt H x).source)  := by sorry

def riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.sum fun α : M =>
    (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))


lemma riemannianMeasure_def
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) :
    riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : M =>
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x)))  := by sorry

lemma measurable_ofReal_pou_weight
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M) :
    Measurable (fun x : M => ENNReal.ofReal (ρ α x))  := by sorry

theorem riemannianMeasure_lintegral_eq
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(riemannianMeasure (I := I) g ρ) =
      ∑' α : M, ∫⁻ x, ENNReal.ofReal (ρ α x) * f x
          ∂(chartLocalMeasure (I := I) g α)  := by sorry

theorem riemannianMeasure_lintegral_finset_le
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {f : M → ℝ≥0∞} (hf : Measurable f) (s : Finset M) :
    ∑ α ∈ s, ∫⁻ x, ENNReal.ofReal (ρ α x) * f x
        ∂(chartLocalMeasure (I := I) g α)
      ≤ ∫⁻ x, f x ∂(riemannianMeasure (I := I) g ρ)  := by sorry

theorem chartLocalMeasure_withDensity_le_riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M) :
    (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))
      ≤ riemannianMeasure (I := I) g ρ  := by sorry

end Measure
end Integral
end DifferentialGeometry
