import Mathlib

namespace DifferentialGeometry
open Bundle
open scoped Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
abbrev SmoothRiemannianMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)

end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow
open Bundle
open scoped Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem tensorPouSobolevHilbert_embedding_Ck
    {g : SmoothRiemannianMetric I M} {r s k m : ℕ}
    (_h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    ∃ C : ℝ, 0 ≤ C := by
  sorry

end DifferentialGeometry.PDE.RicciFlow
