import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.Basic
import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import dep.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Mixed
import dep.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
open DifferentialGeometry.Tensor.Multilinear

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

private theorem fderivWithin_eq_sum_basis_coord
    {F : E -> E} {u : Set E} {y Xy : E}
    (hF : DifferentiableWithinAt 𝕜 F u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 F u y Xy =
      ∑ i : CoordinateIdx (𝕜 := 𝕜) E,
        fderivWithin 𝕜
          (fun z : E => (Module.finBasis 𝕜 E).coord i (F z)) u y Xy •
          (Module.finBasis 𝕜 E) i  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
private theorem fderivWithin_chart_scalar_eq_mvfderiv
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (φ : E -> 𝕜) (f : M -> 𝕜)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x₀)
    (heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) :
    fderivWithin 𝕜 φ (Set.range I) (extChartAt I x₀ x₀)
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E))
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I) (extChartAt I x₀ x₀))) =
      mvfderiv (I := I) f x₀ (X x₀)  := by sorry

omit [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
private theorem tangentFieldModelInChart_fderivWithin_eq_sum_mvfderiv_coord
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E))
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I) (extChartAt I x₀ x₀))) =
      ∑ i : CoordinateIdx (𝕜 := 𝕜) E,
        mvfderiv (I := I)
          (fun p : M =>
            (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p))) x₀ (X x₀) •
          (Module.finBasis 𝕜 E) i  := by sorry

omit [IsManifold I ∞ M] in
theorem covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : MDiffAt (T% V) x₀)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : CoordinateIdx (𝕜 := 𝕜) E,
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
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E))
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I) (extChartAt I x₀ x₀))) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀))  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
private theorem tangentFieldModelInChart_center_symmL
    (V : (x : M) -> TangentSpace I x) (x₀ : M) :
    (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) =
      V x₀  := by sorry

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] [IsManifold I ∞ M] in
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

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] [IsManifold I ∞ M] in
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

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] [IsManifold I ∞ M] in
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
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E))
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I) (extChartAt I x₀ x₀))) =
      mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀)  := by sorry

omit [IsManifold I ∞ M] in
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
    (hcoord : ∀ a : Fin s, ∀ i : CoordinateIdx (𝕜 := 𝕜) E,
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
private theorem tangentFieldModelInChart_contDiffWithinAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContDiffWithinAt 𝕜 (∞ : WithTop ℕ∞)
      (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
      (Set.range I) (extChartAt I x₀ x₀)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
private theorem tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    DifferentiableWithinAt 𝕜
      (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
      (Set.range I) (extChartAt I x₀ x₀)  := by sorry

omit [IsManifold I 2 M] in
private theorem tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M =>
        (Module.finBasis 𝕜 E).coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p))) x₀  := by sorry

omit [IsManifold I 2 M] in
theorem tensor0S_eval_coordinateFrame_contMDiffAt
    {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M => α y (fun a : Fin s => coordinateFrameAt (I := I) x₀ (slots a) y))
      x₀  := by sorry

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
private theorem coordinateFrame_covariantDeriv_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (coordinateFrameAt (I := I) x₀ j) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀  := by sorry

omit [IsManifold I 2 M] in
theorem tensor0S_eval_coordinateFrame_covariantDerivative_slot_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) (a : Fin s) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        α p
          (Function.update
            (fun b : Fin s => coordinateFrameAt (I := I) x₀ (slots b) p)
            a
            ((cov (coordinateFrameAt (I := I) x₀ (slots a)) p) (X p))))
      x₀  := by sorry

theorem nabla0SFun_eval_coordinateFrame_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α p)
          (fun a : Fin s => coordinateFrameAt (I := I) x₀ (slots a) p)) x₀  := by sorry

theorem nabla0SFun_contMDiff_of_eval_coordinateFrame_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hcoeff : ∀ x₀ : M, ∀ slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E,
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s cov X α p)
            (fun a : Fin s => coordinateFrameAt (I := I) x₀ (slots a) p))
        x₀) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s
    ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α p⟩ :
          TotalSpace (Tensor0SModel s 𝕜 E) (fun p : M => Tensor0SSpace s I p)))  := by sorry

theorem nabla0SFun_contMDiff
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s
    ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α p⟩ :
          TotalSpace (Tensor0SModel s 𝕜 E) (fun p : M => Tensor0SSpace s I p)))  := by sorry

noncomputable def nabla0SCoord (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) s
  ⟨fun p : M =>
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α p,
    nabla0SFun_contMDiff (I := I) cov hcov X α⟩

@[simp] theorem nabla0SCoord_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (p : M) :
    nabla0SCoord (I := I) s cov hcov X α p =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α p  := by sorry

end DifferentialGeometry.Tensor.Coordinates

