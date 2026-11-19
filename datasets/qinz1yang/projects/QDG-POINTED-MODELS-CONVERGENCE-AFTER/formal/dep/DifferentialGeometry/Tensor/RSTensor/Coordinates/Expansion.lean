import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import dep.DifferentialGeometry.Tensor.Alternating.Composition
import dep.DifferentialGeometry.Tensor.Multilinear.Composition
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import dep.DifferentialGeometry.Tensor.Multilinear.Smoothness.LinearIsometry
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import dep.DifferentialGeometry.Tensor.RSTensor.Defs
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import dep.DifferentialGeometry.Tensor.Multilinear.Curry.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis

set_option autoImplicit false

noncomputable section


namespace DifferentialGeometry
namespace Tensor0SBundle

open Bundle Module
open scoped Manifold BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section ModelBasis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

end ModelBasis

section Tensor0S

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {s : Nat} {x : M}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem tensor0S_sum_apply {ι : Type*} [Fintype ι]
    (T : ι -> Tensor0SSpace s I x) (v : Fin s -> TangentSpace I x) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v  := by sorry

omit [DecidableEq Idx] in
theorem basisTensor0S_apply
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (slots : Fin s -> Idx) (v : Fin s -> TangentSpace I x) :
    basisTensor0S (I := I) basis slots v =
      ∏ a : Fin s, basis.coord (slots a) (v a)  := by sorry

omit [DecidableEq Idx] in
theorem tensor0S_apply_eq_sum
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) (v : Fin s -> TangentSpace I x) :
    A v =
      ∑ slots : Fin s -> Idx,
        component0S (I := I) basis A slots *
          ∏ a : Fin s, basis.coord (slots a) (v a)  := by sorry

end Tensor0S

end Tensor0SBundle
end DifferentialGeometry

