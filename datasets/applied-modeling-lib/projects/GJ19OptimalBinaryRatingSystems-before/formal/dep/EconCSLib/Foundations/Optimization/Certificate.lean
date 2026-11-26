import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Compact

namespace EconCSLib

namespace Optimization

open scoped BigOperators

/-- `x` maximizes `objective` over the feasible region. -/
def IsMaximizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → objective y ≤ objective x

/-- `x` minimizes `objective` over the feasible region. -/
def IsMinimizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → objective x ≤ objective y

/-- Strict sufficient condition for a unique maximizer. -/
def IsStrictMaximizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → y ≠ x → objective y < objective x

/-- Strict sufficient condition for a unique minimizer. -/
def IsStrictMinimizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → y ≠ x → objective x < objective y

/--
`x` is lexicographically maximal: every feasible alternative has either a
strictly smaller primary objective, or the same primary objective and no larger
secondary objective.
-/
def IsLexicographicMaximizerOn {α : Type*} (feasible : α → Prop)
    (primary secondary : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y →
    primary y < primary x ∨
      (primary y = primary x ∧ secondary y ≤ secondary x)

namespace IsMaximizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

end IsMaximizerOn

namespace IsLexicographicMaximizerOn

variable {α : Type*} {feasible : α → Prop}
  {primary secondary : α → ℝ} {x y : α}

end IsLexicographicMaximizerOn

namespace IsMinimizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

end IsMinimizerOn

namespace IsStrictMaximizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

end IsStrictMaximizerOn

namespace IsStrictMinimizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

end IsStrictMinimizerOn

/--
A maximization certificate: the candidate is feasible, has value `value`, and
`value` upper-bounds every feasible objective value.
-/
structure UpperBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  upper_bound : ∀ y, feasible y → objective y ≤ value

/--
A minimization certificate: the candidate is feasible, has value `value`, and
`value` lower-bounds every feasible objective value.
-/
structure LowerBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  lower_bound : ∀ y, feasible y → value ≤ objective y

/-- A strict maximization certificate proving uniqueness by strict upper bounds. -/
structure StrictUpperBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  strict_upper_bound : ∀ y, feasible y → y ≠ candidate → objective y < value

/-- A strict minimization certificate proving uniqueness by strict lower bounds. -/
structure StrictLowerBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  strict_lower_bound : ∀ y, feasible y → y ≠ candidate → value < objective y

namespace UpperBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

end UpperBoundCertificate

namespace LowerBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

end LowerBoundCertificate

namespace StrictUpperBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

end StrictUpperBoundCertificate

namespace StrictLowerBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

end StrictLowerBoundCertificate

/--
A pointwise certificate that an algorithm returns a minimizer and satisfies an
abstract operation-count bound.

The operation model is deliberately a parameter: downstream modules can use
Turing-machine time, comparison counts, arithmetic-operation counts, or
application-level pseudocode costs while reusing the same optimality wrapper.
-/
structure AlgorithmMinimizerCertificate {Input Output : Type*}
    (algorithm : Input → Output)
    (feasible : Input → Output → Prop)
    (objective : Input → Output → ℝ)
    (operationCount operationBound : Input → ℕ) where
  optimal : ∀ input, IsMinimizerOn (feasible input) (objective input) (algorithm input)
  operationCount_le : ∀ input, operationCount input ≤ operationBound input

/--
A pointwise certificate that an algorithm returns a maximizer and satisfies an
abstract operation-count bound.
-/
structure AlgorithmMaximizerCertificate {Input Output : Type*}
    (algorithm : Input → Output)
    (feasible : Input → Output → Prop)
    (objective : Input → Output → ℝ)
    (operationCount operationBound : Input → ℕ) where
  optimal : ∀ input, IsMaximizerOn (feasible input) (objective input) (algorithm input)
  operationCount_le : ∀ input, operationCount input ≤ operationBound input

/--
A pointwise certificate that an algorithm's output satisfies a specification
and has an abstract operation-count bound.

Use this for soundness claims that are not optimization problems, such as
preprocessing, reduction, feasibility filtering, or verified transformations.
-/
structure AlgorithmSoundnessCertificate {Input Output : Type*}
    (algorithm : Input → Output)
    (specification : Input → Output → Prop)
    (operationCount operationBound : Input → ℕ) where
  sound : ∀ input, specification input (algorithm input)
  operationCount_le : ∀ input, operationCount input ≤ operationBound input

/--
Certificate for a feasible, objective-preserving transform of a minimization
algorithm's output.

This packages the common pattern used by robust-output and postprocessing
arguments: a base algorithm is already certified optimal, the transformed
output is feasible and has the same objective value on every input, and the
transformed implementation satisfies the advertised operation-count bound.
-/
structure MinimizerOutputTransformCertificate {Input Output : Type*}
    (baseAlgorithm transformedAlgorithm : Input → Output)
    (feasible : Input → Output → Prop)
    (objective : Input → Output → ℝ)
    (baseOperationCount transformedOperationCount operationBound :
      Input → ℕ) where
  baseCert :
    AlgorithmMinimizerCertificate baseAlgorithm feasible objective
      baseOperationCount operationBound
  transformed_feasible :
    ∀ input, feasible input (transformedAlgorithm input)
  transformed_objective_eq :
    ∀ input,
      objective input (transformedAlgorithm input) =
        objective input (baseAlgorithm input)
  transformedOperationCount_le :
    ∀ input, transformedOperationCount input ≤ operationBound input

namespace AlgorithmMinimizerCertificate

variable {Input Output : Type*} {algorithm : Input → Output}
  {feasible : Input → Output → Prop} {objective : Input → Output → ℝ}
  {operationCount operationBound : Input → ℕ}

end AlgorithmMinimizerCertificate

namespace MinimizerOutputTransformCertificate

variable {Input Output : Type*}
  {baseAlgorithm transformedAlgorithm : Input → Output}
  {feasible : Input → Output → Prop} {objective : Input → Output → ℝ}
  {baseOperationCount transformedOperationCount operationBound : Input → ℕ}

end MinimizerOutputTransformCertificate

namespace AlgorithmMaximizerCertificate

variable {Input Output : Type*} {algorithm : Input → Output}
  {feasible : Input → Output → Prop} {objective : Input → Output → ℝ}
  {operationCount operationBound : Input → ℕ}

end AlgorithmMaximizerCertificate

namespace AlgorithmSoundnessCertificate

variable {Input Output : Type*} {algorithm : Input → Output}
  {specification : Input → Output → Prop}
  {operationCount operationBound : Input → ℕ}

end AlgorithmSoundnessCertificate

end Optimization

end EconCSLib
