module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Separation.Basic

@[expose] public section

universe u

open Set

/-- A partition of a topological space whose parts are all locally closed. -/
@[stacks 09XZ "locally closed parts"]
structure LocallyClosedPartition (X : Type u) [TopologicalSpace X] where
  /-- The underlying set-theoretic partition. -/
  toPartitions : Setoid.Partitions X
  /-- Every part of the underlying partition is locally closed. -/
  locallyClosed (s : toPartitions.toSet) : IsLocallyClosed (s : Set X)

namespace LocallyClosedPartition

variable {X : Type u} [TopologicalSpace X]

/-- The set of parts of a locally closed partition. -/
abbrev toSet (P : LocallyClosedPartition X) : Set (Set X) :=
  P.toPartitions.toSet

end LocallyClosedPartition
