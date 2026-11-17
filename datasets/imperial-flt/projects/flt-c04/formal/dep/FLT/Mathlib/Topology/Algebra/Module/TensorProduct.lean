module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import dep.FLT.Mathlib.LinearAlgebra.TensorProduct.FiniteFree

@[expose] public section

open scoped TensorProduct

/-- The canonical continuous M-linear isomorphism `M ⊗[R] V ≃ (ι → M)`
where V is a finite free R-module with basis indexed by `ι`, `M` is a commutative
`R`-algebra, and `M ⊗[R] V` has the `M`-module topology. -/
noncomputable def ContinuousLinearEquiv.chooseBasisPiScalarRight' (R M V : Type*)
    [CommRing M] [CommRing R] [Algebra R M]
    [TopologicalSpace M] [IsTopologicalRing M]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [TopologicalSpace (M ⊗[R] V)] [IsTopologicalAddGroup (M ⊗[R] V)]
    [IsModuleTopology M (M ⊗[R] V)] :
    (M ⊗[R] V) ≃L[M] (Module.Free.ChooseBasisIndex R V → M) := {
  __ := (LinearEquiv.chooseBasisPiScalarRight R M V)
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    (LinearEquiv.chooseBasisPiScalarRight R M V).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    (LinearEquiv.chooseBasisPiScalarRight R M V).symm.toLinearMap
  }

namespace ContinuousLinearMap

end ContinuousLinearMap
