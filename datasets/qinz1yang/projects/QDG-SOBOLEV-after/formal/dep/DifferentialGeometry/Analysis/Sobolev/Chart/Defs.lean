import dep.DifferentialGeometry.Integral.Measure.Glue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist



noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]




def chartPushed
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y)) *
      u ((extChartAt I α).symm (toEuclidean.symm y))


def chartTargetEuclid (α : M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  toEuclidean '' (extChartAt I α).target




end Chart
end Sobolev
end Analysis
end DifferentialGeometry
end
