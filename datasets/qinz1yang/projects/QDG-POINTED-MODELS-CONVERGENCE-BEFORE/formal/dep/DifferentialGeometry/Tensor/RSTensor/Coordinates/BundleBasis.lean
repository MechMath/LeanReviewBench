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
open DifferentialGeometry.Tensor.Multilinear

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section



open Bundle Set ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

section HomBasis

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [FiniteDimensional 𝕜 U]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

noncomputable def continuousLinearMapHomBasis
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W) :
    Module.Basis (κ × ι) 𝕜 (U →L[𝕜] W) :=
  (bU.linearMap bW).map
    (LinearMap.toContinuousLinearMap : (U →ₗ[𝕜] W) ≃ₗ[𝕜] U →L[𝕜] W)

theorem continuousLinearMap_homBasis_repr
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W)
    (A : U →L[𝕜] W) (i : ι) (j : κ) :
    (continuousLinearMapHomBasis (𝕜 := 𝕜) bU bW).repr A (j, i) =
      bW.repr (A (bU i)) j  := by sorry

end HomBasis

noncomputable def tensorRSModelBasis {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ) :
    Module.Basis ((Fin r → Fin d) × (Fin s → Fin d)) 𝕜 (TensorRSModel r s 𝕜 E) :=
  let bR := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r
  let bS := continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE s
  (continuousLinearMapHomBasis (𝕜 := 𝕜) bR bS).reindex
    (Equiv.prodComm (Fin s → Fin d) (Fin r → Fin d))

theorem tensorRSModel_basis_repr {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ)
    (A : TensorRSModel r s 𝕜 E)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    (tensorRSModelBasis (𝕜 := 𝕜) (E := E) bE r s).repr A (ρ, σ) =
      (A ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a))  := by sorry

section SmoothCriterion

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_tensorRSModel_of_apply_basis_eval_basis
    {d r s : ℕ} (bE : Module.Basis (Fin d) 𝕜 E)
    {G : M → TensorRSModel r s 𝕜 E} {x₀ : M} {n : WithTop ℕ∞}
    (hcoord :
      ∀ ρ : Fin r → Fin d, ∀ σ : Fin s → Fin d,
        ContMDiffAt I 𝓘(𝕜, 𝕜) n
          (fun p : M =>
            (G p ((continuousMultilinearMapBasis
              (𝕜 := 𝕜) (F := E) bE r) ρ))
              (fun a : Fin s => bE (σ a))) x₀) :
    ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n G x₀  := by sorry

end SmoothCriterion

section Trivialization

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x₀ x : M}

namespace Tensor0SSpace

noncomputable def constInChart (s : ℕ) (x₀ : M)
    (β : Tensor0SModel s 𝕜 E) (x : M) : Tensor0SSpace s I x := by
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  exact (trivializationAt (Tensor0SModel s 𝕜 E)
    (fun x => Tensor0SSpace s I x) x₀).symmL 𝕜 x β

omit [CompleteSpace 𝕜] in
theorem trivializationAt_apply (s : ℕ)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T⟩).2 v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))  := by sorry

omit [CompleteSpace 𝕜] in
theorem continuousLinearEquivAt_apply (s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearEquivAt 𝕜 x
          (show x ∈ (trivializationAt (Tensor0SModel s 𝕜 E)
            (fun x => Tensor0SSpace s I x) x₀).baseSet from hx) T) v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))  := by sorry

omit [CompleteSpace 𝕜] in
theorem continuousLinearMapAt_apply (s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))  := by sorry

omit [CompleteSpace 𝕜] in
theorem constInChart_apply (s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (β : Tensor0SModel s 𝕜 E) (v : Fin s → TangentSpace I x) :
    (constInChart (𝕜 := 𝕜) (I := I) s x₀ β x) v =
      β (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (v i))  := by sorry

end Tensor0SSpace

namespace TensorRSSpace

omit [CompleteSpace 𝕜] in
theorem trivializationAt_apply (r s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x) (β : Tensor0SModel r 𝕜 E) (v : Fin s → E) :
    letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    (((trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2 β) v =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v a))  := by sorry

theorem trivializationAt_basis_coord {d r s : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    (((trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2
        ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a)) =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x
          ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) bE r) ρ)))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (bE (σ a)))  := by sorry

end TensorRSSpace

end Trivialization

end

end Tensor0SBundle
end DifferentialGeometry

