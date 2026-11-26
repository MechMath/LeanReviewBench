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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
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
import dep.PRPKG24AccuracyDiversity.Basic

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
Expected satisfaction from `q` independent Bernoulli items when the user consumes one item:
`1 - (1 - p)^q`.
-/
noncomputable def bernoulliAtLeastOneValue (p : ℝ) (q : ℕ) : ℝ :=
  1 - (1 - p) ^ q

/-- Bernoulli-satisfaction specialization used by the paper's heterogeneous Bernoulli results. -/
structure BernoulliSatisfactionModel (T : ℕ) where
  likelihood : ItemType T → ℝ
  successProb : ItemType T → ℝ

namespace BernoulliSatisfactionModel

/-- Convert the Bernoulli satisfaction model into the generic consumption model. -/
noncomputable def toConsumptionModel {T : ℕ} (B : BernoulliSatisfactionModel T) : ConsumptionModel T where
  likelihood := B.likelihood
  valueOfCount := fun t q => bernoulliAtLeastOneValue (B.successProb t) q

/-- Objective for the Bernoulli satisfaction model. -/
noncomputable def objective {T : ℕ}
    (B : BernoulliSatisfactionModel T) (a : CountAllocation T) : ℝ := B.toConsumptionModel.objective a

end BernoulliSatisfactionModel

end PRPKG24AccuracyDiversity
