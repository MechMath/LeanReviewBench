import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProductMeasure

open MeasureTheory

open ProbabilityTheory

namespace EconCSLib

namespace FairCoin

noncomputable def fairMeasure : Measure Bool :=
  ((PMF.bernoulli (1 / 2 : NNReal) (sorry)).toMeasure : Measure Bool)

noncomputable def productMeasure (ι : Type*) : Measure (ι → Bool) :=
  Measure.infinitePi (fun _ : ι => fairMeasure)

end FairCoin

end EconCSLib
