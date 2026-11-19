import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.Basic
import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import dep.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Mixed
import dep.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative

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


theorem nabla0S_one_model_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      modelDeriv0SAt (I := I) X x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)  := by sorry

theorem nabla0S_one_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (j : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          1 cov X α x₀)
        (fun _ : Fin 1 => j) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)  := by sorry

theorem nabla0SFun_one_eval_coordFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (j : CoordinateIdx (𝕜 := 𝕜) E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀)
        (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) (fun _ : Fin 1 => j) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)  := by sorry

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem tensor0S_one_eval_coordFrame_sum
    {x₀ : M}
    (αx : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (Z : TangentSpace I x₀) :
    αx (fun _ : Fin 1 => Z) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (coordinateFrameAtToBasis (I := I) x₀).coord j Z *
          αx (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j x₀)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem tensor0S_one_eval_finset_sum
    {ι : Type*} {x : M}
    (αx : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1 x)
    (t : Finset ι) (V : ι -> TangentSpace I x) :
    αx (fun _ : Fin 1 => t.sum V) =
      t.sum (fun i => αx (fun _ : Fin 1 => V i))  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
private theorem mdifferentiableAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem oneForm_mvfderiv_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    mvfderiv (I := I) (t.sum f) x v =
      t.sum (fun i => mvfderiv (I := I) (f i) x v)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem oneForm_mvfderiv_mul
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x)
    (hg : MDifferentiableAt I 𝓘(𝕜, 𝕜) g x) :
    mvfderiv (I := I) (fun y : M => f y * g y) x v =
      f x * mvfderiv (I := I) g x v +
        mvfderiv (I := I) f x v * g x  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem oneForm_covariantDerivative_finset_sum
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (t : Finset ι) (σ : ι -> (x : M) -> TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v)  := by sorry

omit [IsManifold I 1 M] [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem oneForm_coordinateFrame_coeff_at_base_eq_coord
    (x₀ : M) (Z : TangentSpace I x₀) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j x₀ Z =
      (coordinateFrameAtToBasis (I := I) x₀).coord j Z  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem oneForm_mvfderiv_congr_eventually
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    mvfderiv (I := I) f x v = mvfderiv (I := I) g x v  := by sorry

end DifferentialGeometry.Tensor.Coordinates

