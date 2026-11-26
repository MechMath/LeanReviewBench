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
import dep.LG21TestOptionalPolicies.MainTheorems

namespace LG21TestOptionalPolicies

noncomputable section

open EconCSLib.Probability

/--
Proposition 4.2 Gaussian-law core: a strict access-side Gaussian mean gap
supplies the law difference needed by the four-group proof.
-/
theorem paper_interface_proposition4_2_not_law_latent_skill_fair_of_gaussian_mean_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianVarianceLaw}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    {Llow Lhigh : GaussianVarianceLaw}
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh : S.latentAccessLaw e qHigh base = Lhigh)
    (hAccessLow : S.latentAccessLaw e qLow base = Llow)
    (hmean : Llow.mean < Lhigh.mean) :
    ¬ lg21SourceLawLatentSkillFair S := sorry

end

end LG21TestOptionalPolicies
