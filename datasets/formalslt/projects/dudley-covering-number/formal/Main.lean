import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import dep.Covering.FiniteSubGaussianChaining
import dep.Covering.TotalBoundedDudley
import dep.Covering.UnitIntervalDudley
import dep.Rademacher.FiniteSample

namespace FormalSLT.Covering.ContinuousDudleyUnitIntervalCovering

open scoped BigOperators Interval

open MeasureTheory

open FormalSLT.Covering.FiniteSubGaussianChaining



open FormalSLT.Covering.UnitIntervalDudley



noncomputable section

/-- Dyadic level selected by the half-open, right-closed annulus
`(1 / 2^(j+2), 1 / 2^(j+1)]`.

For positive radii this is `⌊log_2 (1 / ε)⌋ - 1`. Values outside the positive
Dudley interval are harmless default values for the surrounding concrete
capstone. -/
def unitIntervalCoveringIndex (ε : ℝ) : ℕ :=
  Nat.floor (Real.logb 2 ε⁻¹) - 1

/-- Real-radius covering staircase for the unit interval. At dyadic radius
`1 / 2^(j+1)` it is the genuine adjacent rounded-grid finite-cover product. -/
def unitIntervalCoveringNumber (ε : ℝ) : ℕ :=
  unitIntervalRoundedDyadicGridCoverCount (unitIntervalCoveringIndex ε)

/-- Entropy integrand built from the genuine covering-number staircase. -/
def unitIntervalCoveringEntropyAtRadius (ε : ℝ) : ℝ :=
  Real.sqrt (Real.log (unitIntervalCoveringNumber ε : ℝ))

/-- Continuous Dudley entropy-integral bound for the unit-interval process
using the genuine real-radius covering-number staircase. -/
-- fidelity: the entropy integrand is `sqrt (log (unitIntervalCoveringNumber ε))`,
-- with dyadic samples equal to the genuine rounded-grid finite-cover products.
theorem continuous_dudley_entropy_integral_iSup_unitInterval_coveringNumber :
    finiteExpectation unitIntervalRademacherLinearProcess.weight
        unitIntervalRademacherLinearSup ≤
      1 + 4 * Real.sqrt
          (2 * unitIntervalRademacherLinearProcess.varianceProxy) *
        (∫ ε in (0 : ℝ)..((1 : ℝ) / 2),
          unitIntervalCoveringEntropyAtRadius ε) := sorry

end

end FormalSLT.Covering.ContinuousDudleyUnitIntervalCovering
