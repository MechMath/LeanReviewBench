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
import Mathlib.Analysis.Convex.StdSimplex
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

open AppliedModelingLib

namespace PRPKG24AccuracyDiversity

namespace CountAllocation

end CountAllocation

/-- A plain target representation profile. -/
structure HomogeneityProfile (T : ℕ) where
  targetShare : ItemType T → ℝ

namespace HomogeneityProfile

end HomogeneityProfile

/--
A γ-homogeneity profile, represented by abstract target weights.

In the paper, the intended target weights are usually proportional to powers of type
likelihoods. We keep the weight function explicit here so the discrete finite layer does
not depend on real-power API details before the asymptotic branch is started.
-/
structure GammaHomogeneityProfile (T : ℕ) where
  gamma : ℝ
  targetWeight : ItemType T → ℝ

namespace GammaHomogeneityProfile

/-- Normalizer for the target weights. -/
noncomputable def normalizer {T : ℕ} (G : GammaHomogeneityProfile T) : ℝ := ∑ t, G.targetWeight t

/-- Target share induced by the γ-profile weights, with zero fallback if the normalizer is zero. -/
noncomputable def targetShare {T : ℕ} (G : GammaHomogeneityProfile T) (t : ItemType T) : ℝ :=
  if h : G.normalizer = 0 then 0 else G.targetWeight t / G.normalizer

end GammaHomogeneityProfile

end PRPKG24AccuracyDiversity

namespace PRPKG24AccuracyDiversity

namespace CountAllocation

end CountAllocation

namespace HomogeneityProfile

end HomogeneityProfile

namespace GammaHomogeneityProfile

end GammaHomogeneityProfile

end PRPKG24AccuracyDiversity
