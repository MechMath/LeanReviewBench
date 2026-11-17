module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction

@[expose] public section

variable {G M : Type*} [TopologicalSpace G] [SMul G M]

/--
`ContinuousSMulDiscrete G M` means that the action `G × M → M` is continuous
when `M` is given the discrete topology (See `continuousSMulDiscrete_iff`).

This class is especially useful when `M` already has another topology and we cannot easily put the
discrete topology on it.
-/
class ContinuousSMulDiscrete (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  isOpen_smul_eq (G) (x y : M) : IsOpen { g : G | g • x = y }

instance (priority := low) [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMulDiscrete G M] : ContinuousSMul G M := sorry
