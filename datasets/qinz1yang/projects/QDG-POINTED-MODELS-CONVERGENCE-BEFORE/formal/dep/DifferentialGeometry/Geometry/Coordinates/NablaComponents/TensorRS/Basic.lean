import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.Tensor0S
import dep.DifferentialGeometry.Geometry.Coordinates.Fields.Tensor
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents
import dep.DifferentialGeometry.Tensor.RSTensor.Field
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.TensorRS
import dep.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set DifferentialGeometry.Tensor0SBundle DifferentialGeometry.TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

def coordDerivRSAt {r s : ℕ}
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  let β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r x :=
    Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r x₀ β₀
  mvfderiv (I := I)
    (fun y : M =>
      (T y (β y))
        (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
    x₀ (X x₀)


def modelDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let X' : E → E := fun z =>
    tangentSpaceModelContinuousLinearEquiv z
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (fun x => X x) (Set.range I) z)
  let T' : E -> TensorRSModel r s 𝕜 E :=
    tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ T
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  (fderivWithin 𝕜 T'
      (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
      (extChartAt I x₀ x₀)
      (X' (extChartAt I x₀ x₀))
    β₀)
    (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))

def ModelDerivEqCoordDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x) :
    Prop :=
  forall upper lower,
    modelDerivRSAt (I := I) X x₀ T upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ T upper lower

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
private theorem mdifferentiableAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem mvfderiv_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    mvfderiv (I := I) (t.sum f) x v =
      t.sum (fun i => mvfderiv (I := I) (f i) x v)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem mvfderiv_mul
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x)
    (hg : MDifferentiableAt I 𝓘(𝕜, 𝕜) g x) :
    mvfderiv (I := I) (fun y : M => f y * g y) x v =
      f x * mvfderiv (I := I) g x v +
        mvfderiv (I := I) f x v * g x  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem mvfderiv_congr_eventually
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    mvfderiv (I := I) f x v = mvfderiv (I := I) g x v  := by sorry

end DifferentialGeometry.Tensor.Coordinates

