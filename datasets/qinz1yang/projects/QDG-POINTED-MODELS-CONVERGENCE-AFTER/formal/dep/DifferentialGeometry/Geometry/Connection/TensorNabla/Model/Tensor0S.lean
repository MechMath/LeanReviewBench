import dep.DifferentialGeometry.Geometry.LieDerivative.Tensor
import dep.DifferentialGeometry.Tensor.RSTensor.Defs
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
import dep.DifferentialGeometry.Tensor.Multilinear.Curry.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorField.Pullback
import dep.DifferentialGeometry.Tensor.RSTensor.Field
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open Bundle Set IsManifold ContinuousLinearMap VectorField Filter
    DifferentialGeometry.Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelAt_apply_slots {s : ℕ}
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → E) :
    covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α slots =
      dα_X slots -
        ∑ a : Fin s, α (Function.update slots a (ΓX (slots a)))  := by sorry

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_apply_slots {s : ℕ}
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E)
    (slots : Fin s → E) :
    covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E) s X ΓX α u x slots =
      fderivWithin 𝕜 α u x (X x) slots -
        ∑ a : Fin s, α x (Function.update slots a (ΓX x (slots a)))  := by sorry

theorem lieDeriv_correctionL_apply_slots {s : ℕ}
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → E) :
    (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX α) slots =
      ∑ a : Fin s, α (Function.update slots a (ΓX (slots a)))  := by sorry

omit [CompleteSpace 𝕜] in
theorem fderivWithin_tensor0SModel_eval_linear_slots {s : ℕ}
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (L : Fin s → E → 𝕜 →L[𝕜] E)
    (u : Set E) (y Xy : E)
    (hα : DifferentiableWithinAt 𝕜 α u y)
    (hL : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (L a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y)
    (c : Fin s → 𝕜) :
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => L a z (c a))) u y Xy =
      fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (c a)) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => L b y (c b)) a
            (fderivWithin 𝕜 (L a) u y Xy (c a)))  := by sorry

omit [CompleteSpace 𝕜] in
theorem fderivWithin_tensor0SModel_eval_slots {s : ℕ}
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (V : Fin s → E → E)
    (u : Set E) (y Xy : E)
    (hα : DifferentiableWithinAt 𝕜 α u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => V a z)) u y Xy =
      fderivWithin 𝕜 α u y Xy (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy))  := by sorry

end ModelCovariantDerivative

end

end TensorLieDeriv
end DifferentialGeometry

