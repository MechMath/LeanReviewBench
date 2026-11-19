import Mathlib

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem time_dependent_vf_chart_local_picard_with_lipschitz
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (_hCont :
      ContinuousOn (Function.uncurry (fun t x => X t x)) (Set.univ : Set (ℝ × M)))
    (_hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ U : Set M, IsOpen U ∧ α ∈ U ∧ U ⊆ (chartAt H α).source ∧
      ∃ φ : ℝ → M → M,
        (∀ x ∈ U, φ 0 x = x) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x ∈ U,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => φ s x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (φ t x))) := by sorry
end DifferentialGeometry.PDE.RicciFlow.ODE
