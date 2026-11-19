import dep.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Pointwise
open DifferentialGeometry.Tensor.Multilinear
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

omit [CompleteSpace E] in
theorem exists_contMDiffSection_eventuallyEq_tangentConstAt
    [T2Space M] (x : M) (v : TangentSpace I x) :
    ∃ V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      (fun p : M => V p) =ᶠ[𝓝 x] tangentConstAt (I := I) x v ∧ V x = v  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    {x : M} (X Y Z : TangentSpace I x)
    (Xs Ys Zs :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hX : (fun p : M => Xs p) =ᶠ[𝓝 x] tangentConstAt (I := I) x X)
    (hY : (fun p : M => Ys p) =ᶠ[𝓝 x] tangentConstAt (I := I) x Y)
    (hZ : (fun p : M => Zs p) =ᶠ[𝓝 x] tangentConstAt (I := I) x Z) :
    connectionRiemannCurvatureField cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      connectionRiemannCurvatureField cov
        (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) x  := by sorry

theorem riemannCurvatureAt_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    riemannCurvatureAt cov hcov x α (vec3 (X x) (Y x) (Z x)) =
      cotangentToDual α
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x)  := by sorry

theorem riemannCurvature04At_apply_smooth
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z W : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    riemannCurvature04At g cov hcov x (vec4 (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x)
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x)  := by sorry

private theorem riemannCurvatureAt_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    letI := tensorRSBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1 3
    letI := tensorRSBundleFiber (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1 3
    letI := tensorRSBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1 3
    letI := tensorRSBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 1 3
    ContMDiff I (I.prod 𝓘(Real, TensorRSModel 1 3 Real E)) (∞ : WithTop ℕ∞)
      (fun x : M =>
        (⟨x, riemannCurvatureAt (I := I) cov hcov x⟩ :
          TotalSpace (TensorRSModel 1 3 Real E)
            (fun x : M =>
              TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3 x)))  := by sorry

noncomputable def rm13Section
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    Tensor13Section (I := I) (M := M) :=
  by
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    exact
      ⟨fun x => riemannCurvatureAt cov hcov x,
        riemannCurvatureAt_contMDiff (I := I) cov hcov⟩

@[simp]
theorem rm13Section_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    rm13Section (I := I) (M := M) cov hcov x =
      riemannCurvatureAt cov hcov x  := by sorry

theorem rm13Section_apply_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    rm13Section (I := I) (M := M) cov hcov x α (vec3 X Y Z) =
      cotangentToDual α
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)  := by sorry

theorem rm13Section_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    rm13Section (I := I) (M := M) cov hcov x α (vec3 (X x) (Y x) (Z x)) =
      cotangentToDual α
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x)  := by sorry

private theorem riemannCurvature04At_contMDiff
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    letI := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 4
    ContMDiff I (I.prod 𝓘(Real, Tensor0SModel 4 Real E)) (∞ : WithTop ℕ∞)
      (fun x : M =>
        (⟨x, riemannCurvature04At (I := I) g cov hcov x⟩ :
          TotalSpace (Tensor0SModel 4 Real E)
            (fun x : M =>
          Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)))  := by sorry

noncomputable def rm04Section
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    Tensor04Section (I := I) (M := M) :=
  ⟨fun x => riemannCurvature04At g cov hcov x,
    riemannCurvature04At_contMDiff (I := I) g cov hcov⟩

@[simp]
theorem rm04Section_apply
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    rm04Section (I := I) (M := M) g cov hcov x =
      riemannCurvature04At g cov hcov x  := by sorry

theorem rm04Section_apply_const
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    {x : M}
    (X Y Z W : TangentSpace I x) :
    rm04Section (I := I) (M := M) g cov hcov x (vec4 X Y Z W) =
      g.inner x W
        (connectionRiemannCurvatureField cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)  := by sorry

theorem rm04Section_apply_smooth
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (X Y Z W : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    rm04Section (I := I) (M := M) g cov hcov x
        (vec4 (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x)
        (connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x)  := by sorry

noncomputable def ricciSection
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M] :
    Tensor02Section (I := I) (M := M) :=
  by
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    exact tensorRSFieldApplyInput (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞
      (contractTensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := ∞) 0 2 (rm13Section (I := I) (M := M) cov hcov))
      (Tensor0SField.one0 (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞)

@[simp]
theorem ricciSection_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    ricciSection (I := I) (M := M) cov hcov x =
      ricciCurvatureAt cov hcov x  := by sorry

theorem ricciSection_eq_trace
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    [T2Space M]
    (x : M) :
    ricciSection (I := I) (M := M) cov hcov x =
      ricciFromRm13At (I := I) (M := M)
        (rm13Section (I := I) (M := M) cov hcov x)  := by sorry

end CovariantDerivative

end DifferentialGeometry.Geometry.Curvature

