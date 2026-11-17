import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MBJG25ProducerFairness

open scoped BigOperators

/-- The variance of the estimated quality.
    Source status: direct paper formula
    Paper Definition:
    $\frac{t q_v (1 - q_v)}
            {(\eta(\widetilde{\alpha}+\widetilde{\beta}) + t)^2}$
-/
noncomputable def paper_variance (alpha beta eta t q_v : ℝ) : ℝ :=
  t * q_v * (1 - q_v) / (eta * alpha + eta * beta + t) ^ 2

/--
Theorem 3.1, strict decrease on interior quality values.
For `0 < q_v < 1`, positive prior-shape mass, positive number of prior samples,
and stronger prior strength `η_high > η_low`, variance is strictly decreasing.
Source status: corrected source statement
Source note: The paper states strict variance decrease without excluding boundary qualities; this formal statement adds `0 < q_v < 1` because variance is identically zero at `q_v = 0` and `q_v = 1`.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_interior
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 < q)
    (hq1 : q < 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_lt : etaLow < etaHigh) :
    paper_variance alpha beta etaHigh t q <
      paper_variance alpha beta etaLow t q := sorry

end MBJG25ProducerFairness
