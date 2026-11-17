import Mathlib
import dep.EconCSLib.Foundations.Probability.Gaussian

open Filter MeasureTheory ProbabilityTheory Set Function

open scoped ENNReal NNReal Real Topology

namespace EconCSLib

namespace Probability

noncomputable section

def standardGaussianMeasure : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

private instance : IsProbabilityMeasure standardGaussianMeasure := sorry

private instance : NullSingletonClass standardGaussianMeasure := sorry

namespace GaussianScaleLaw

end GaussianScaleLaw

end

end Probability

end EconCSLib
