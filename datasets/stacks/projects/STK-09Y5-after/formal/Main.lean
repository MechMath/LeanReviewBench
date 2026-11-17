module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Separation.Basic
public import dep.ReasLib.Topology.Stratification.Good
public import dep.ReasLib.Topology.Stratification.Indexed
public import dep.ReasLib.Topology.Stratification.Partition

@[expose] public section

universe u v

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

namespace LocallyClosedPartition

/-- `Q` is a finite good refinement of the locally closed partition `P`: it has finitely many
parts, refines `P`, and satisfies the frontier condition. -/
@[stacks 09Y5 "finite good locally closed refinement"]
structure IsFiniteGoodRefinement (Q P : LocallyClosedPartition X) : Prop where
  /-- The refining partition has finitely many parts. -/
  finite : Q.toSet.Finite
  /-- The refining partition refines the given partition. -/
  refines : Q.Refines P
  /-- The refining partition satisfies the frontier condition. -/
  isGood : Q.IsGood

end LocallyClosedPartition

namespace FiniteStratification

end FiniteStratification

namespace LocallyClosedPartition

/-- A finite partition of a Noetherian space into locally closed parts admits a finite good
locally closed refinement. -/
@[stacks 09Y5 "finite good refinement in a Noetherian space"]
theorem exists_finite_good_refinement [NoetherianSpace X]
    (P : LocallyClosedPartition X) (hPfinite : P.toSet.Finite) :
    ∃ Q : LocallyClosedPartition X, Q.IsFiniteGoodRefinement P := sorry

end LocallyClosedPartition
