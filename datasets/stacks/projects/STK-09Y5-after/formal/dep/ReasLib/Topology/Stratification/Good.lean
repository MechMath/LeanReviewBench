module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Separation.Basic
public import dep.ReasLib.Topology.Stratification.Partition

@[expose] public section

universe u

open Set TopologicalSpace

namespace LocallyClosedPartition

variable {X : Type u} [TopologicalSpace X]

/-- A locally closed partition satisfies the frontier condition when a part meeting the closure of
another is contained in that closure. -/
@[stacks 09Y0 "good stratifications"]
structure IsGood (P : LocallyClosedPartition X) : Prop where
  /-- A part meeting the closure of another part lies in that closure. -/
  frontier_condition (S T : P.toSet) (hST : ((S : Set X) ∩ closure (T : Set X)).Nonempty) :
    (S : Set X) ⊆ closure (T : Set X)

end LocallyClosedPartition
