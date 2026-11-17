import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact
import dep.AppliedModelingLib.Applications.RecommenderSystems.Allocation
import dep.AppliedModelingLib.Foundations.Probability.PMFKernel
import dep.PRPKG24AccuracyDiversity.GeneralRounding

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

namespace AppendixD1GenericPower

/-- The normalizer of positive target weights. -/
noncomputable def weightSum {κ : Type*} [Fintype κ] (w : κ -> ℝ) : ℝ :=
  ∑ i, w i

/-- The normalized target share associated with strictly positive weights. -/
noncomputable def targetShare {κ : Type*} [Fintype κ]
    (w : κ -> ℝ) (i : κ) : ℝ := w i / weightSum w

/-- The source weight corresponding to the corrected D.1(iv) power profile. -/
noncomputable def sourcePowerWeight
    {κ : Type*} (p : κ -> ℝ) (sigma : ℝ) (i : κ) : ℝ :=
  p i ^ (1 / (1 - sigma))

end AppendixD1GenericPower

end PRPKG24AccuracyDiversity
