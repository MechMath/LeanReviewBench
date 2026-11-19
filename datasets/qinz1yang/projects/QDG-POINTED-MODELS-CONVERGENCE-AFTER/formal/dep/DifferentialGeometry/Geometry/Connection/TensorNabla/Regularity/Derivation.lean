import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.RawDefs.MCovariant
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.RawDefs.Bundled
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
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
import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import dep.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Mixed
import dep.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import dep.DifferentialGeometry.Bundle.TangentSpace

namespace DifferentialGeometry
namespace Tensor0SBundle

open Bundle Set DifferentialGeometry.TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private noncomputable def vectorFieldModelPullbackWithin (x₀ : M)
    (X : (x : M) → TangentSpace I x) (z : E) : E :=
  tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) z
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      X (Set.range I) z)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
theorem vector_field_model_pullback_within_eq_mpullback_within (x₀ : M)
    (X : (x : M) → TangentSpace I x) (z : E) :
    vectorFieldModelPullbackWithin (I := I) x₀ X z =
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        X (Set.range I) z  := by sorry

private theorem fderivWithin_eq_sum_basis_coord
    {F : E -> E} {u : Set E} {y Xy : E}
    (hF : DifferentiableWithinAt 𝕜 F u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 F u y Xy =
      ∑ i : Fin (Module.finrank 𝕜 E),
        fderivWithin 𝕜
          (fun z : E => (Module.finBasis 𝕜 E).coord i (F z)) u y Xy •
          (Module.finBasis 𝕜 E) i  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
private theorem fderivWithin_chart_scalar_eq_mvfderiv
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (φ : E -> 𝕜) (f : M -> 𝕜)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x₀)
    (heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) :
    fderivWithin 𝕜 φ (Set.range I) (extChartAt I x₀ x₀)
        (vectorFieldModelPullbackWithin (I := I) x₀ (fun x => X x)
          (extChartAt I x₀ x₀)) =
      mvfderiv (I := I) f x₀ (X x₀)  := by sorry

private theorem tangentFieldModelInChart_fderivWithin_eq_sum_mvfderiv_coord
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (vectorFieldModelPullbackWithin (I := I) x₀ (fun x => X x)
          (extChartAt I x₀ x₀)) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        mvfderiv (I := I)
          (fun p : M =>
            (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p))) x₀ (X x₀) •
          (Module.finBasis 𝕜 E) i  := by sorry

theorem covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : MDiffAt (T% V) x₀)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun p : M => (cov V p) (X p)) (extChartAt I x₀ x₀) =
      fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (vectorFieldModelPullbackWithin (I := I) x₀ (fun x => X x)
          (extChartAt I x₀ x₀)) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀))  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
private theorem tangentFieldModelInChart_center_symmL
    (V : (x : M) -> TangentSpace I x) (x₀ : M) :
    (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) =
      V x₀  := by sorry

omit [CompleteSpace 𝕜] in
private theorem tensor0SModelInChart_apply_modelSlots_center {s : ℕ}
    (A : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀)
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
            (extChartAt I x₀ x₀)) =
      A x₀ (fun a : Fin s => V a x₀)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem tensor0SModelInChart_apply_update_modelSlot_center {s : ℕ}
    (A : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (W : (x : M) -> TangentSpace I x) (x₀ : M) (a : Fin s) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀)
        (Function.update
          (fun b : Fin s =>
            tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
              (extChartAt I x₀ x₀))
          a
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
            (extChartAt I x₀ x₀))) =
      A x₀ (Function.update (fun b : Fin s => V b x₀) a (W x₀))  := by sorry

omit [CompleteSpace 𝕜] in
private theorem fderivWithin_tensor0S_eval_modelSlots_center_eq_mvfderiv {s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ (fun x => α x) y
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (vectorFieldModelPullbackWithin (I := I) x₀ (fun x => X x)
          (extChartAt I x₀ x₀)) =
      mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem fderivWithin_localTensor0S_eval_modelSlots_center_eq_mvfderiv {s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ β y
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (vectorFieldModelPullbackWithin (I := I) x₀ (fun x => X x)
          (extChartAt I x₀ x₀)) =
      mvfderiv (I := I) (fun p : M => β p (fun a : Fin s => V a p))
        x₀ (X x₀)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem fderivWithin_tensorRS_eval_modelSlots_center_eq_mvfderiv {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r s x₀ (fun x => T x) y
            (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r x₀ β y))
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (vectorFieldModelPullbackWithin (I := I) x₀ (fun x => X x)
          (extChartAt I x₀ x₀)) =
      mvfderiv (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀)  := by sorry

noncomputable def localCovariantDerivTensor0SAt (r : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M) : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x₀ := by
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  exact (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).symm x₀
    (covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E) r
      (vectorFieldModelPullbackWithin (I := I) x₀ (fun x => X x))
      (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))

theorem localCovariantDerivTensor0SAt_eval_moving {r : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin r -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin r => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin r, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin r,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin r, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
      (fun a : Fin r => V a x₀) =
      mvfderiv (I := I) (fun p : M => β p (fun a : Fin r => V a p))
        x₀ (X x₀) -
        ∑ a : Fin r,
          β x₀
            (Function.update (fun b : Fin r => V b x₀) a
              ((cov (V a) x₀) (X x₀)))  := by sorry

omit [CompleteSpace 𝕜] in
private theorem tensorRSModelInChart_apply_modelSlots_center {r s : ℕ}
    (A : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x)
    (βm : Tensor0SModel r 𝕜 E) (slots : Fin s -> E) (x₀ : M) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ A (extChartAt I x₀ x₀) βm) slots =
      (A x₀
        ((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀ βm))
        (fun a : Fin s =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
            (slots a))  := by sorry

omit [CompleteSpace 𝕜] in
private theorem tensorRSModelInChart_apply_update_modelOutputSlot_center {r s : ℕ}
    (A : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (W : (x : M) -> TangentSpace I x) (x₀ : M) (a : Fin s) :
    (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ A (extChartAt I x₀ x₀)
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r x₀ β (extChartAt I x₀ x₀)))
        (Function.update
          (fun b : Fin s =>
            tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
              (extChartAt I x₀ x₀))
          a
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
            (extChartAt I x₀ x₀))) =
      (A x₀ (β x₀)) (Function.update (fun b : Fin s => V b x₀) a (W x₀))  := by sorry

theorem localCovDeriv0S_sub {r : ℕ}
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin r -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin r => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin r, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin r,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin r, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀
        (fun a : Fin r => V a x₀) -
      localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀
        (fun a : Fin r => V a x₀)) =
      -∑ a : Fin r,
        β x₀
          (Function.update (fun b : Fin r => V b x₀) a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀)))  := by sorry

theorem nablaRSFun_eval_moving {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) =
      mvfderiv (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀)))  := by sorry

theorem nablaRSFun_connection_difference_apply {r s : ℕ}
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀ (β x₀) (fun a : Fin s => V a x₀) -
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov' X T x₀ (β x₀) (fun a : Fin s => V a x₀)) =
      -(((T x₀
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀)) -
        ((T x₀
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀))
          (fun a : Fin s => V a x₀))) -
      ∑ a : Fin s,
        (T x₀ (β x₀))
          (Function.update (fun b : Fin s => V b x₀) a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀)))  := by sorry

theorem nabla0SFun_eval_coordFrame_moving {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀)
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x₀) (fun a : Fin s => V a x₀) =
      mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀)))  := by sorry

end Tensor0SBundle
end DifferentialGeometry

