


import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {d : ℕ}

def Module.Basis.cDualBasis [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (B : Module.Basis (Fin d) 𝕜 E) :
    Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜) :=
  B.dualBasis.map LinearMap.toContinuousLinearMap

@[simp]
theorem Module.Basis.cDualBasis_apply_self [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (B : Module.Basis (Fin d) 𝕜 E) (i j : Fin d) :
    B.cDualBasis i (B j) = if i = j then (1 : 𝕜) else 0  := by sorry

theorem exists_predual_basis [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (b : Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜)) :
    ∃ B : Module.Basis (Fin d) 𝕜 E,
      ∀ i j, b i (B j) = if i = j then 1 else 0  := by sorry

theorem cdual_sum_repr {d : ℕ} [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (b : Module.Basis (Fin d) 𝕜 E) (α : E →L[𝕜] 𝕜) :
    (∑ k, (α (b k)) • LinearMap.toContinuousLinearMap (b.coord k)) = α  := by sorry

