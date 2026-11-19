import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.Basic

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
variable [IsManifold I 1 M] [IsManifold I 2 M] [h_mfd : IsManifold I ∞ M]

omit [CompleteSpace 𝕜] [IsManifold I 2 M] in
theorem tensor0S_two_eval_coordFrame_sum
    {x₀ : M}
    (Ax : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 2 x₀)
    (Y Z : TangentSpace I x₀) :
    Ax (fun q : Fin 2 => if q = 0 then Y else Z) =
      ∑ i : CoordinateIdx (𝕜 := 𝕜) E, ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (coordinateFrameAtToBasis (I := I) x₀).coord i Y *
          (coordinateFrameAtToBasis (I := I) x₀).coord j Z *
          Ax (fun q : Fin 2 =>
            if q = 0 then coordinateFrameAt (I := I) x₀ i x₀
            else coordinateFrameAt (I := I) x₀ j x₀)  := by sorry

omit [IsManifold I 2 M] in
omit h_mfd in
theorem tensor0S_two_symm_of_coordFrame
    {Idx : Type*} [Finite Idx]
    {x₀ : M}
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x₀))
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 2 x₀)
    (hcoord : ∀ i j : Idx,
      A (fun q : Fin 2 => if q = 0 then basis i else basis j) =
        A (fun q : Fin 2 => if q = 0 then basis j else basis i)) :
    ∀ Y Z : TangentSpace I x₀,
      A (fun q : Fin 2 => if q = 0 then Y else Z) =
        A (fun q : Fin 2 => if q = 0 then Z else Y)  := by sorry

section TopRegularity

omit h_mfd in
theorem nabla0S_two_model_coord [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (j l : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x₀)
        (fun q : Fin 2 => if q = 0 then j else l) =
      modelDeriv0SAt (I := I) X x₀ (fun x => A x)
        (fun q : Fin 2 => if q = 0 then j else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) l k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then j else k)  := by sorry

omit h_mfd in
theorem nabla0S_two_coord [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (j l : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x₀)
        (fun q : Fin 2 => if q = 0 then j else l) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
        (fun q : Fin 2 => if q = 0 then j else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) l k *
          coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then j else k)  := by sorry

omit h_mfd in
theorem nabla0SFun_two_eval_coordFrame [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (j l : CoordinateIdx (𝕜 := 𝕜) E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀)
        (fun q : Fin 2 =>
          if q = 0 then coordinateFrameAt (I := I) x₀ j x₀
          else coordinateFrameAt (I := I) x₀ l x₀) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
        (fun q : Fin 2 => if q = 0 then j else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) l k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then j else k)  := by sorry

omit h_mfd in
theorem nabla0SFun_two_eval_coordFrame_symm_of_symm [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (hsymm : ∀ y : M, ∀ U V : TangentSpace I y,
      A y (fun q : Fin 2 => if q = 0 then U else V) =
        A y (fun q : Fin 2 => if q = 0 then V else U))
    (j l : CoordinateIdx (𝕜 := 𝕜) E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀)
        (fun q : Fin 2 =>
          if q = 0 then coordinateFrameAt (I := I) x₀ j x₀
          else coordinateFrameAt (I := I) x₀ l x₀) =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        2 cov X A x₀)
          (fun q : Fin 2 =>
            if q = 0 then coordinateFrameAt (I := I) x₀ l x₀
            else coordinateFrameAt (I := I) x₀ j x₀)  := by sorry

omit h_mfd in
theorem nabla0SFun_two_symm_of_symm [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M)
    (hsymm : ∀ y : M, ∀ U V : TangentSpace I y,
      A y (fun q : Fin 2 => if q = 0 then U else V) =
        A y (fun q : Fin 2 => if q = 0 then V else U))
    (Y Z : TangentSpace I x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀) (fun q : Fin 2 => if q = 0 then Y else Z) =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        2 cov X A x₀) (fun q : Fin 2 => if q = 0 then Z else Y)  := by sorry

omit h_mfd in
theorem nabla0SFun_two_eval_coordFrame_expanded [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (Y Z : TangentSpace I x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀) (fun q : Fin 2 => if q = 0 then Y else Z) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E, ∑ l : CoordinateIdx (𝕜 := 𝕜) E,
        (coordinateFrameAtToBasis (I := I) x₀).coord j Y *
          (coordinateFrameAtToBasis (I := I) x₀).coord l Z *
          (coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
              (fun q : Fin 2 => if q = 0 then j else l) -
            ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) j k *
                coordComponent0SAt (I := I) (A x₀)
                  (fun q : Fin 2 => if q = 0 then k else l) -
            ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) l k *
                coordComponent0SAt (I := I) (A x₀)
                  (fun q : Fin 2 => if q = 0 then j else k))  := by sorry

end TopRegularity

end DifferentialGeometry.Tensor.Coordinates

