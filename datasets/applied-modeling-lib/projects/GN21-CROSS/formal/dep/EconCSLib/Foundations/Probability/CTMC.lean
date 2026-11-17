import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace EconCSLib

open scoped Topology

open Filter

/--
Closed-form probability that a two-state CTMC currently in state `i` is in the
opposite state `j` after elapsed time `t`.

The rates are `lambdaIJ` for transitions from `i` to `j` and `lambdaJI` for
transitions from `j` back to `i`.
-/
noncomputable def twoStateCtmcSwitchProb (lambdaIJ lambdaJI t : ℝ) : ℝ :=
  lambdaIJ / (lambdaIJ + lambdaJI) *
    (1 - Real.exp (-(lambdaIJ + lambdaJI) * t))

end EconCSLib
