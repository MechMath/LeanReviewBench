module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sober

@[expose] public section

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- Every irreducible closed subset of a Hausdorff space is a singleton. -/
@[stacks 004Y "irreducible closed subsets of Hausdorff spaces are singletons"]
theorem TopologicalSpace.IrreducibleCloseds.exists_eq_singleton [T2Space X] (Z : IrreducibleCloseds X) :
    ∃ x : X, Z = {x} := sorry
