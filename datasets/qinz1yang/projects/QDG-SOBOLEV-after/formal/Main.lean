import Mathlib
import dep.DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
namespace DifferentialGeometry.PDE.RicciFlow
open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

theorem tensorPouSobolevHilbert_embedding_Ck
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {r s k m : ℕ}
    (_h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤
          C *
            ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
 sorry
end DifferentialGeometry.PDE.RicciFlow
