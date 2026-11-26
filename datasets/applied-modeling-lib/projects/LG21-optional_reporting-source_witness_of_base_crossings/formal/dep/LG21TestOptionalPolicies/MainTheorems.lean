import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import dep.EconCSLib.Foundations.Probability.Gaussian

open EconCSLib

open EconCSLib.Probability

namespace LG21TestOptionalPolicies

noncomputable section

/-- Source access indicator `Z`: a student either has access to the test or not. -/
inductive LG21AccessStatus where
  | noAccess
  | access
deriving DecidableEq

namespace LG21AccessStatus

end LG21AccessStatus

/--
The school's information set in Sections 3--4.  `accessStatus = none` is the
Section 3 case where the school does not observe `Z`; `some z` is the Section 4
case where `Z` is included in the information set.  The test score is present
exactly when the student reports it.
-/
structure LG21SchoolInformationSet (Base Test : Type*) where
  accessStatus : Option LG21AccessStatus
  baseProfile : Base
  reportsScore : Bool
  reportedTestScore : Option Test

/--
Paper-local law type for LG21 statements that compare deterministic
Bayesian estimates with genuinely Gaussian posterior-score laws.
-/
inductive LG21EstimateLaw where
  | point : ℝ → LG21EstimateLaw
  | gaussian : GaussianScaleLaw → LG21EstimateLaw

namespace LG21EstimateLaw

end LG21EstimateLaw

/--
Paper-local representation of Gaussian estimate laws and finite mixtures over
base profiles.  It is used for Proposition 4.3's demographic statement, where
the paper integrates base-conditioned estimate laws over the common
base-profile distribution.
-/
inductive LG21GaussianMixtureLaw (Base : Type*) where
  | gaussian : GaussianScaleLaw → LG21GaussianMixtureLaw Base
  | finiteMixture :
      PMF Base → (Base → GaussianScaleLaw) → LG21GaussianMixtureLaw Base

namespace LG21GaussianMixtureLaw

end LG21GaussianMixtureLaw

/-- Definition 1 action object for students with test access: `(Y, X)`. -/
structure LG21AccessAction where
  takesTest : Bool
  reportsScore : Bool
deriving DecidableEq, Repr

namespace LG21AccessAction

end LG21AccessAction

namespace LG21SchoolInformationSet

end LG21SchoolInformationSet

/--
The three source requirement policies: no additional reporting requirement,
reporting required conditional on taking, and reporting required given access.
-/
inductive LG21RequirementPolicy where
  | noRequirements
  | reportRequiredConditionalTaking
  | reportRequiredGivenAccess
deriving DecidableEq

namespace LG21RequirementPolicy

end LG21RequirementPolicy

/--
Definition 1 student information for a student with test access.  The `test`
field is the realized optional test score that the reporting decision can use.
-/
structure LG21AccessStudentInfo (Skill Base Test : Type*) where
  skill : Skill
  base : Base
  test : Test

namespace LG21AccessStudentInfo

end LG21AccessStudentInfo

/--
Source-shaped witness for Theorem 3.1's optional-reporting case.  The paper's
first bullet says all access students take the test, while reporting follows a
finite lower cutoff in the realized test score at each base profile.
-/
structure LG21OptionalReportingStrategicWithholdingSourceWitness
    (Base : Type*) where
  reports : Base → ℝ → Prop
  takes : Base → ℝ → Prop
  all_take : ∀ base skill, takes base skill
  some_access_students_do_not_report : ∃ base score, ¬ reports base score
  reporting_threshold :
    ∀ base, ∃ cutoff : ℝ, ∀ score : ℝ, reports base score ↔ cutoff ≤ score

end

end LG21TestOptionalPolicies
