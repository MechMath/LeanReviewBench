import dep.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option autoImplicit false

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type _} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CovariantDerivative

omit [FiniteDimensional ℝ E] in
private theorem connectionRiemannCurvatureField_tangentConst_add_first
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X₁ X₂ Y Z : TangentSpace I x) :
    connectionRiemannCurvatureField cov
        (tangentConstAt (I := I) x (X₁ + X₂))
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X₁)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x +
        connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X₂)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem connectionRiemannCurvatureField_tangentConst_smul_first
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    connectionRiemannCurvatureField cov
        (tangentConstAt (I := I) x (a • X))
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      a • connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem connectionRiemannCurvatureField_tangentConst_add_second
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y₁ Y₂ Z : TangentSpace I x) :
    connectionRiemannCurvatureField cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x (Y₁ + Y₂))
        (tangentConstAt (I := I) x Z) x =
      connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y₁)
          (tangentConstAt (I := I) x Z) x +
        connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y₂)
          (tangentConstAt (I := I) x Z) x  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem connectionRiemannCurvatureField_tangentConst_smul_second
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    connectionRiemannCurvatureField cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x (a • Y))
        (tangentConstAt (I := I) x Z) x =
      a • connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem connectionRiemannCurvatureField_tangentConst_add_third
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y Z₁ Z₂ : TangentSpace I x) :
    connectionRiemannCurvatureField cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x (Z₁ + Z₂)) x =
      connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z₁) x +
        connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z₂) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem connectionRiemannCurvatureField_tangentConst_smul_third
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    connectionRiemannCurvatureField cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x (a • Z)) x =
      a • connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x  := by sorry

private noncomputable def riemannCurvatureZCLM
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    TangentSpace I x →L[Real] Real :=
  let _ : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Z =>
        cotangentToDual α
          (connectionRiemannCurvatureField cov
            (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
            (tangentConstAt (I := I) x Z) x)
      map_add' := by
        intro Z₁ Z₂
        change
          cotangentToDual α
              (connectionRiemannCurvatureField cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x (Z₁ + Z₂)) x) =
            cotangentToDual α
                (connectionRiemannCurvatureField cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z₁) x) +
              cotangentToDual α
                (connectionRiemannCurvatureField cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z₂) x)
        rw [connectionRiemannCurvatureField_tangentConst_add_third cov hcov x X Y Z₁ Z₂]
        exact map_add (cotangentToDual α) _ _
      map_smul' := by
        intro a Z
        change
          cotangentToDual α
              (connectionRiemannCurvatureField cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x (a • Z)) x) =
            a • cotangentToDual α
              (connectionRiemannCurvatureField cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x Z) x)
        rw [connectionRiemannCurvatureField_tangentConst_smul_third cov hcov x a X Y Z]
        exact map_smul (cotangentToDual α) a _ }

omit [CompleteSpace E] in
@[simp] private theorem riemannCurvatureZCLM_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    riemannCurvatureZCLM cov hcov x α X Y Z =
      cotangentToDual α
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)  := by sorry

private noncomputable def riemannCurvatureYZModel
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X : TangentSpace I x) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 1) (Ei := fun _ : Fin 2 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun Y =>
          (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
            (riemannCurvatureZCLM cov hcov x α X Y)
        map_add' := by
          intro Y₁ Y₂
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change
            cotangentToDual α
                (connectionRiemannCurvatureField cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x (Y₁ + Y₂))
                  (tangentConstAt (I := I) x Z) x) =
              cotangentToDual α
                  (connectionRiemannCurvatureField cov
                    (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y₁)
                    (tangentConstAt (I := I) x Z) x) +
                cotangentToDual α
                  (connectionRiemannCurvatureField cov
                    (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y₂)
                    (tangentConstAt (I := I) x Z) x)
          rw [connectionRiemannCurvatureField_tangentConst_add_second cov hcov x X Y₁ Y₂ Z]
          exact map_add (cotangentToDual α) _ _
        map_smul' := by
          intro a Y
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change
            cotangentToDual α
                (connectionRiemannCurvatureField cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x (a • Y))
                  (tangentConstAt (I := I) x Z) x) =
              a • cotangentToDual α
                (connectionRiemannCurvatureField cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z) x)
          rw [connectionRiemannCurvatureField_tangentConst_smul_second cov hcov x a X Y Z]
          exact map_smul (cotangentToDual α) a _ })

@[simp] private theorem riemannCurvatureYZModel_apply_vec2
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
  riemannCurvatureYZModel cov hcov x α X (vec2 Y Z) =
      cotangentToDual α
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)  := by sorry

private noncomputable def riemannCurvatureModel
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 2) (Ei := fun _ : Fin 3 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X => riemannCurvatureYZModel cov hcov x α X
        map_add' := by
          intro X₁ X₂
          apply ContinuousMultilinearMap.ext
          intro v
          have hv : v = vec2 (v 0) (v 1) := by
            funext i
            fin_cases i <;> simp [vec2]
          rw [hv]
          simp only [riemannCurvatureYZModel_apply_vec2]
          rw [connectionRiemannCurvatureField_tangentConst_add_first cov hcov x X₁ X₂ (v 0) (v 1)]
          exact map_add (cotangentToDual α) _ _
        map_smul' := by
          intro a X
          apply ContinuousMultilinearMap.ext
          intro v
          have hv : v = vec2 (v 0) (v 1) := by
            funext i
            fin_cases i <;> simp [vec2]
          rw [hv]
          simp only [riemannCurvatureYZModel_apply_vec2]
          rw [connectionRiemannCurvatureField_tangentConst_smul_first cov hcov x a X (v 0) (v 1)]
          exact map_smul (cotangentToDual α) a _ })


noncomputable def riemannCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor13At (I := I) (M := M) x :=
  TensorRSSpace.ofModel (I := I) (x := x)
    (LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        riemannCurvatureModel cov hcov x
          (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α)
      map_add' := by
        intro α β
        apply ContinuousMultilinearMap.ext
        intro v
        let R := connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x (v 0)) (tangentConstAt (I := I) x (v 1))
          (tangentConstAt (I := I) x (v 2)) x
        change cotangentToDual (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (α + β)) R =
          cotangentToDual (I := I)
              (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α) R +
            cotangentToDual (I := I)
              (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) β) R
        have hαβ :
            Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (α + β) =
              Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α +
                Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) β := by
          exact map_add
            (tensor0SSpaceContinuousLinearEquiv (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x).symm α β
        rw [hαβ]
        rfl
      map_smul' := by
        intro c α
        apply ContinuousMultilinearMap.ext
        intro v
        let R := connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x (v 0)) (tangentConstAt (I := I) x (v 1))
          (tangentConstAt (I := I) x (v 2)) x
        change cotangentToDual (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (c • α)) R =
          c • cotangentToDual (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α) R
        have hα :
            Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (c • α) =
              c • Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α := by
          exact map_smul
            (tensor0SSpaceContinuousLinearEquiv (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x).symm c α
        rw [hα]
        rfl })

@[simp]
theorem riemannCurvatureAt_apply_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    riemannCurvatureAt cov hcov x α (vec3 X Y Z) =
      cotangentToDual α
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)  := by sorry

private noncomputable def tangentFlatCotangentModelCLM
    (g : SmoothRiemannianMetric I M) (x : M) :
    E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 1 => E) Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W =>
        (continuousMultilinearCurryFin1 Real E Real).symm
          (LinearMap.toContinuousLinearMap ((tangentFlatLinear (I := I) g x) W))
      map_add' := by
        intro W W'
        apply (continuousMultilinearCurryFin1 Real E Real).injective
        ext V
        change
          ((tangentFlatLinear (I := I) g x) (W + W')) V =
            (((tangentFlatLinear (I := I) g x) W) +
              ((tangentFlatLinear (I := I) g x) W')) V
        exact congrArg (fun L : Module.Dual Real (TangentSpace I x) => L V)
          ((tangentFlatLinear (I := I) g x).map_add W W')
      map_smul' := by
        intro c W
        apply (continuousMultilinearCurryFin1 Real E Real).injective
        ext V
        change
          ((tangentFlatLinear (I := I) g x) (c • W)) V =
            (c • ((tangentFlatLinear (I := I) g x) W)) V
        exact congrArg (fun L : Module.Dual Real (TangentSpace I x) => L V)
          ((tangentFlatLinear (I := I) g x).map_smul c W) }

omit [CompleteSpace E] in
@[simp] private theorem tangentFlatCotangentModelCLM_apply
    (g : SmoothRiemannianMetric I M) (x : M) (W : TangentSpace I x) :
    tangentFlatCotangentModelCLM (I := I) g x W =
      (continuousMultilinearCurryFin1 Real E Real).symm
        (LinearMap.toContinuousLinearMap ((tangentFlatLinear (I := I) g x) W))  := by sorry

noncomputable def riemannCurvature04At
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor04At (I := I) (M := M) x :=
  tensor04StandardOfOutAt (I := I) (M := M)
    (Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (ContinuousLinearMap.uncurryLeft
        (𝕜 := Real) (n := 3) (Ei := fun _ : Fin 4 => E) (G := Real)
        (((TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (riemannCurvatureAt cov hcov x)).comp
          (tangentFlatCotangentModelCLM (I := I) g x)) :
          E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real)))

@[simp]
theorem riemannCurvature04At_apply_const
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (X Y Z W : TangentSpace I x) :
    riemannCurvature04At g cov hcov x (vec4 X Y Z W) =
      g.inner x W
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)  := by sorry

noncomputable def ricciCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  ricciFromRm13At (riemannCurvatureAt cov hcov x)

@[simp]
theorem ricciCurvatureAt_eq_trace
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    ricciCurvatureAt cov hcov x = ricciFromRm13At (riemannCurvatureAt cov hcov x)  := by sorry

theorem riemannCurvature04At_eq_lower_riemannCurvatureAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (X Y Z W : TangentSpace I x) :
    riemannCurvature04At g cov hcov x (vec4 X Y Z W) =
      riemannCurvatureAt cov hcov x (dualToCotangent ((tangentFlatLinear g x) W))
        (vec3 X Y Z)  := by sorry

end CovariantDerivative

end DifferentialGeometry.Geometry.Curvature

