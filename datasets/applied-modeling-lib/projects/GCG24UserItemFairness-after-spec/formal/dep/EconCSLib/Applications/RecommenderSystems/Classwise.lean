import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact
import dep.EconCSLib.Applications.RecommenderSystems.Policy
import dep.EconCSLib.Foundations.Math.FiniteOptimization
import dep.EconCSLib.Foundations.Probability.FiniteExpectation

open scoped BigOperators

namespace EconCSLib

namespace Policy

/--
Chosen representatives for the fibers of `τ`. This is the exact data needed to
turn a classwise policy on `α` into a policy on the class space `κ`.
-/
structure FiberRepresentatives {α κ : Type*} (τ : α → κ) where
  repr : κ → α
  repr_spec : ∀ k, τ (repr k) = k

/-- A surjective classification map has a chosen representative in every fiber. -/
noncomputable def FiberRepresentatives.ofSurjective {α κ : Type*}
    {τ : α → κ} (hτ : Function.Surjective τ) : FiberRepresentatives τ where
  repr := fun k => Classical.choose (hτ k)
  repr_spec := fun k => Classical.choose_spec (hτ k)

end Policy

end EconCSLib
