import Mathlib.Analysis.Calculus.Deriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

theorem maxreg_l2deriv_to_pointwise_hasderivwithinat
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u : ℝ → X) (u' : ℝ → X) (T : ℝ) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt u (u' t) (Set.Ici 0) t := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
