module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Separation.Basic
public import dep.ReasLib.Topology.Stratification.Partition

@[expose] public section

universe u v

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- An ordered, locally closed, pairwise-disjoint cover whose closures are unions of lower
strata. -/
@[stacks 09Y1 "indexed locally closed stratifications"]
structure IsStratification {I : Type v} [PartialOrder I] (strata : I → Set X) : Prop where
  /-- Distinct strata are disjoint. -/
  disjoint : Pairwise fun i j ↦ Disjoint (strata i) (strata j)
  /-- The strata cover the ambient space. -/
  cover : (⋃ i, strata i) = univ
  /-- Each stratum is locally closed. -/
  locallyClosed : ∀ i, IsLocallyClosed (strata i)
  /-- The closure of a stratum is contained in the union of lower strata. -/
  closure_subset : ∀ j, closure (strata j) ⊆ ⋃ i ∈ Set.Iic j, strata i

namespace IsStratification

variable {I : Type v} [PartialOrder I] {strata : I → Set X}

/-- The indices of the nonempty strata. -/
abbrev NonemptyIndex (strata : I → Set X) :=
  { i : I // (strata i).Nonempty }

/-- The family obtained by discarding empty indexed strata. -/
abbrev nonemptyStrata (strata : I → Set X) : NonemptyIndex strata → Set X :=
  fun i ↦ strata i.1

/-- The nonempty strata form a set-theoretic partition. -/
theorem range_nonemptyStrata_isPartition (h : IsStratification strata) :
    Setoid.IsPartition (Set.range (nonemptyStrata strata)) := sorry

/-- The underlying set-theoretic partition of an indexed stratification. -/
noncomputable def toPartitions (h : IsStratification strata) : Setoid.Partitions X :=
  ⟨Set.range (nonemptyStrata strata), h.range_nonemptyStrata_isPartition⟩

end IsStratification

/-- A finite indexed locally closed stratification, with its indexing data available for direct
downstream use. -/
@[stacks 09Y3 "finite stratifications"]
structure FiniteStratification (X : Type u) [TopologicalSpace X] where
  /-- The finite ordered index type. -/
  index : Type v
  /-- Finiteness of the index type. -/
  instFinite : Finite index
  /-- The order controlling frontier relations. -/
  instPartialOrder : PartialOrder index
  /-- The indexed family of strata. -/
  strata : index → Set X
  /-- The stratification conditions on the family of strata. -/
  isStratification : @IsStratification X _ index instPartialOrder strata

namespace FiniteStratification

variable {X : Type u} [TopologicalSpace X]

end FiniteStratification
