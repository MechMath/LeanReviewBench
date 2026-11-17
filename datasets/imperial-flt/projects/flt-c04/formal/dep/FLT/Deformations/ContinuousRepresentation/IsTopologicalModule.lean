module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.MulAction

@[expose] public section

open Topology

variable (R : Type*) [Ring R] [TopologicalSpace R]
  (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]

/--
`IsTopologicalModule R M` states that the topology in `M` makes scalar multiplication and addition
into continuous maps.
-/
class IsTopologicalModule extends ContinuousSMul R M, ContinuousAdd M

variable [IsTopologicalModule R M]

instance Submodule.instIsTopologicalModuleSubtypeMem (S : Submodule R M) : IsTopologicalModule R S
    := sorry

instance Pi.instTopologicalModule {ι : Type*} (R : Type*) [Ring R] [TopologicalSpace R]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsTopologicalModule R (M i)] :
    IsTopologicalModule R ((i : ι) → M i) := sorry
