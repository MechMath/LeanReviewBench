import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.Expansion
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
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
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Section
import dep.DifferentialGeometry.Tensor.Product.Basis
import dep.DifferentialGeometry.Tensor.Product.Bundle
import dep.DifferentialGeometry.Tensor.Product.Pretrivialization
import dep.DifferentialGeometry.Tensor.Product.Defs
import dep.DifferentialGeometry.Tensor.Product.HomEquiv
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import dep.DifferentialGeometry.Tensor.RSTensor.Defs
import dep.DifferentialGeometry.Tensor.Multilinear.Curry.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import dep.DifferentialGeometry.Tensor.Alternating.Curry
import dep.DifferentialGeometry.Tensor.Alternating.Flip
import dep.DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import dep.DifferentialGeometry.Tensor.Alternating.Reindexing.Domain
import Mathlib.LinearAlgebra.Alternating.Basic
import dep.DifferentialGeometry.Tensor.Alternating.Shuffle.Decomposition
import dep.DifferentialGeometry.Tensor.Alternating.Shuffle.Split
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases
import Mathlib.Topology.FiberBundle.Basic
import dep.DifferentialGeometry.Tensor.Product.Fiber
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import dep.DifferentialGeometry.Bundle.Section

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
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

section Covariant

variable {s q : Nat}
variable (basis : Module.Basis Idx 𝕜 (TangentSpace I x))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_add_field
    (A B : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (A + B) slots =
      component0S (I := I) basis A slots + component0S (I := I) basis B slots  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_neg_field
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (-A) slots =
      -component0S (I := I) basis A slots  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_sub_field
    (A B : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (A - B) slots =
      component0S (I := I) basis A slots - component0S (I := I) basis B slots  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_smul_field
    (c : 𝕜) (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (c • A) slots =
      c * component0S (I := I) basis A slots  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_nsmul
    (n : ℕ) (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (n • A) slots =
      n • component0S (I := I) basis A slots  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_product_field
    (A : Tensor0SSpace s I x) (B : Tensor0SSpace q I x)
    (slots : Fin (s + q) -> Idx) :
    component0S (I := I) basis
        (Bundle.continuousMultilinearMap.productFun
          (𝕜 := 𝕜) (F := E) (E := TangentSpace I) A B) slots =
      component0S (I := I) basis A (slots ∘ Fin.castAdd q) *
        component0S (I := I) basis B (slots ∘ Fin.natAdd s)  := by sorry

end Covariant

section Mixed

variable {r s : Nat}
variable (basis : Module.Basis Idx 𝕜 (TangentSpace I x))

def componentRSField
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) : 𝕜 :=
  component0S (I := I) basis (T (basisTensor0S (I := I) basis upper)) lower

omit [DecidableEq Idx] in
@[simp]
theorem componentRSField_apply
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRSField (I := I) basis T upper lower =
      (T (basisTensor0S (I := I) basis upper))
        (fun a => basis (lower a))  := by sorry

omit [DecidableEq Idx] in
theorem componentRSField_congr_slots
    (T : TensorRSSpace r s I x)
    {upper upper' : Fin r -> Idx} {lower lower' : Fin s -> Idx}
    (hu : upper = upper') (hl : lower = lower') :
    componentRSField (I := I) basis T upper lower =
      componentRSField (I := I) basis T upper' lower'  := by sorry

omit [DecidableEq Idx] in
theorem componentRSField_apply_input_eq_sum
    (T : TensorRSSpace r s I x) (input : Tensor0SSpace r I x)
    (lower : Fin s -> Idx) :
    component0S (I := I) basis (T input) lower =
      ∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper *
          componentRSField (I := I) basis T upper lower  := by sorry

omit [DecidableEq Idx] in
theorem extRS_basis_field
    {A B : TensorRSSpace r s I x}
    (h : ∀ upper : Fin r -> Idx, ∀ lower : Fin s -> Idx,
      componentRSField (I := I) basis A upper lower =
        componentRSField (I := I) basis B upper lower) :
    A = B  := by sorry

end Mixed

end Tensor0SBundle
end DifferentialGeometry

