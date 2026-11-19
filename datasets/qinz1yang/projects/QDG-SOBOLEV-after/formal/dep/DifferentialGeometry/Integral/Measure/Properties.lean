import dep.DifferentialGeometry.Integral.Measure.ChartDensity
import dep.DifferentialGeometry.Integral.Measure.Glue
import dep.DifferentialGeometry.Integral.Measure.Invariance
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary



noncomputable section

open Bundle Manifold Set MeasureTheory Function
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




theorem chartLocalMeasure_compact_lt_top
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H x₀).source) :
    chartLocalMeasure (I := I) g x₀ K < (⊤ : ℝ≥0∞)  := by sorry

private lemma pou_term_zero_of_tsupport_disjoint
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {K : Set M} (hK : MeasurableSet K) (α : M)
    (hdisj : Disjoint K (tsupport (ρ α))) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))) K = 0  := by sorry

private lemma pou_term_le_chartLocalMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {K : Set M} (hK : MeasurableSet K) (α : M) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))) K ≤
      chartLocalMeasure (I := I) g α (K ∩ tsupport (ρ α))  := by sorry

theorem riemannianMeasure_compact_lt_top
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    {K : Set M} (hK : IsCompact K) :
    riemannianMeasure (I := I) g ρ K < (⊤ : ℝ≥0∞)  := by sorry

theorem riemannianMeasure_isFiniteMeasureOnCompacts
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    IsFiniteMeasureOnCompacts (riemannianMeasure (I := I) g ρ)  := by sorry

theorem riemannianVolumeMeasure_isFiniteMeasureOnCompacts
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g)  := by sorry

theorem locallyCompactSpace_of_chartedSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E] [FiniteDimensional ℝ E]
    (H : Type*) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    LocallyCompactSpace M  := by sorry

theorem riemannianMeasure_isLocallyFiniteMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    IsLocallyFiniteMeasure (riemannianMeasure (I := I) g ρ)  := by sorry

theorem riemannianVolumeMeasure_isLocallyFiniteMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g)  := by sorry

theorem riemannianMeasure_sigmaFinite
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    SigmaFinite (riemannianMeasure (I := I) g ρ)  := by sorry

theorem riemannianVolumeMeasure_sigmaFinite
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    SigmaFinite (riemannianVolumeMeasure (I := I) (M := M) g)  := by sorry

theorem riemannianMeasure_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    IsFiniteMeasure (riemannianMeasure (I := I) g ρ)  := by sorry

theorem riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g)  := by sorry

private lemma interior_isInteriorPoint_dense :
    Dense ({x : M | I.IsInteriorPoint x} : Set M)  := by sorry

private lemma chartLocalMeasure_open_pos_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    {V : Set M} (hVopen : IsOpen V) {x₁ : M} (hx₁V : x₁ ∈ V)
    (hVsub : V ⊆ (chartAt H α).source)
    (hx₁_int : extChartAt I α x₁ ∈ interior (range I)) :
    0 < chartLocalMeasure (I := I) g α V  := by sorry

private lemma exists_open_nbhd_pou_pos
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    {α : M} {U : Set M} (hUopen : IsOpen U) {x : M} (hxU : x ∈ U)
    (hxpos : 0 < ρ α x) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ V ⊆ (chartAt H α).source ∧
      ∃ c > (0 : ℝ), ∀ y ∈ V, c ≤ ρ α y  := by sorry

theorem riemannianMeasure_isOpenPosMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    (riemannianMeasure (I := I) g ρ).IsOpenPosMeasure  := by sorry

theorem riemannianVolumeMeasure_isOpenPosMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure  := by sorry

theorem riemannianMeasure_regular
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    MeasureTheory.Measure.Regular (riemannianMeasure (I := I) g ρ)  := by sorry

theorem riemannianVolumeMeasure_regular
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    MeasureTheory.Measure.Regular (riemannianVolumeMeasure (I := I) (M := M) g)  := by sorry

end Measure
end Integral
end DifferentialGeometry
