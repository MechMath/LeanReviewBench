import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import dep.EconCSLib.Foundations.Probability.Gaussian

open EconCSLib

open EconCSLib.Probability

namespace LG21TestOptionalPolicies

noncomputable section

/--
Continuous-law version of the source-facing policy surface.

The finite `LG21SourcePolicySurface` above is used for PMF-based resampling
proofs.  The paper's Gaussian impossibility propositions compare equality of
continuous estimate laws, so this parallel surface abstracts over the law type
directly.
-/
structure LG21SourceLawPolicySurface
    (Skill Base Test Law : Type*) where
  Equilibrium : Type*
  latentAccessLaw : Equilibrium → Skill → Base → Law
  latentNoAccessLaw : Equilibrium → Skill → Base → Law
  observableAccessLaw : Equilibrium → Base → Law
  observableNoAccessLaw : Equilibrium → Base → Law
  demographicAccessLaw : Equilibrium → Law
  demographicNoAccessLaw : Equilibrium → Law
  baseOnlyLaw : Equilibrium → Base → Law
  fullFeatureLaw : Equilibrium → Base → Test → Law

/-- Definition 2 over arbitrary law objects. -/
def lg21SourceLawLatentSkillFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e q base, S.latentAccessLaw e q base =
    S.latentNoAccessLaw e q base

end

end LG21TestOptionalPolicies
