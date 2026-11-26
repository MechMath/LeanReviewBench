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

/-- A finite good refinement of a set-theoretic partition. -/
@[stacks 09Y5 "finite good locally closed refinement"]
structure IsFiniteGoodRefinement (Q : LocallyClosedPartition X)
    (P : Setoid.Partitions X) : Prop where
  /-- The refining partition has finitely many parts. -/
  finite : Q.toSet.Finite
  /-- The refining partition refines the given partition. -/
  refines : Q.toPartitions ≤ P
  /-- The refining partition satisfies the frontier condition. -/
  isGood : Q.IsGood

end LocallyClosedPartition

namespace FiniteStratification

end FiniteStratification

/-- A finite partition of a Noetherian space admits a finite good locally closed refinement. -/
@[stacks 09Y5 "finite good refinement in a Noetherian space"]
theorem Setoid.Partitions.exists_finite_good_refinement [NoetherianSpace X]
    (P : Setoid.Partitions X) (hPfinite : P.toSet.Finite) :
    ∃ Q : LocallyClosedPartition X, Q.IsFiniteGoodRefinement P := sorry
