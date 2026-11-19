import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.RawDefs.MCovariant
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.RawDefs.Bundled
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.Expansion
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Endomorphism
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.Tensor0S
import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import dep.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Mixed
import dep.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open Bundle Set IsManifold ContinuousLinearMap DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

section Model

noncomputable def totalCovDerivTensor0SModelAt (s : ℕ)
    (Dα : E →L[𝕜] Tensor0SModel s 𝕜 E) (Γ : E →L[𝕜] E →L[𝕜] E)
    (α : Tensor0SModel s 𝕜 E) : Tensor0SModel (s + 1) 𝕜 E :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := 𝕜) (n := s) (Ei := fun _ : Fin (s + 1) => E) (G := 𝕜)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X =>
          covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
            (Dα X) (Γ X) α
        map_add' := by
          intro X Y
          simp only [map_add]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [lieDeriv_correction_add_right]
          abel
        map_smul' := by
          intro c X
          simp only [map_smul]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [lieDeriv_correction_smul_right]
          ext slots
          simp [sub_eq_add_neg] })

@[simp]
theorem totalCovDeriv_tensor0SModelAt_apply_cons (s : ℕ)
    (Dα : E →L[𝕜] Tensor0SModel s 𝕜 E) (Γ : E →L[𝕜] E →L[𝕜] E)
    (α : Tensor0SModel s 𝕜 E) (X : E) (slots : Fin s → E) :
    totalCovDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s Dα Γ α
        (Fin.cons X slots) =
      covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s (Dα X) (Γ X) α slots  := by sorry

end Model

end

end TensorLieDeriv

namespace Tensor0SBundle

noncomputable section


open Bundle Set IsManifold ContinuousLinearMap DifferentialGeometry.TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]

noncomputable def totalNabla0SFun (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) : Tensor0SSpace (s + 1) I x₀ := by
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + 1)
  exact (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
    (fun x : M => Tensor0SSpace (s + 1) I x) x₀).symm x₀
    (totalCovDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
      (fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s x₀ (fun x => α x))
        (Set.range I) (extChartAt I x₀ x₀))
      (connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀
        (extChartAt I x₀ x₀))
      (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ (α x₀)))

omit [IsManifold I ∞ M] in
theorem totalNabla0SFun_congr (s : ℕ)
    {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α β : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    (hcov : cov = cov') (hα : α = β) (x : M) :
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x =
      totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov' β x  := by sorry

abbrev TotalNabla0SRegular (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) : Prop :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1)
  ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel (s + 1) 𝕜 E)) (∞ : WithTop ℕ∞)
    (fun x : M =>
      (⟨x, totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x⟩ :
        TotalSpace (Tensor0SModel (s + 1) 𝕜 E)
          (fun x : M => Tensor0SSpace (s + 1) I x)))

noncomputable def totalNabla0S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1)
  ⟨totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov α, hreg⟩

omit [IsManifold I ∞ M] in
@[simp] theorem totalNabla0S_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α)
    (x : M) :
    totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg x =
      totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x  := by sorry

omit [IsManifold I ∞ M] in
theorem totalNabla0SFun_apply_tangentConstInChart (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (X : E) (slots : Fin s → E) :
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x₀
        (Fin.cons (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ X x₀)
          (fun a : Fin s => tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a) x₀))
      =
    covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
      (fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s x₀ (fun x => α x))
        (Set.range I) (extChartAt I x₀ x₀) X)
      (connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀
        (extChartAt I x₀ x₀) X)
      (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ (α x₀))
      slots  := by sorry

omit [IsManifold I ∞ M] in
theorem totalNabla0SFun_apply_section (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s → TangentSpace I x) :
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x slots  := by sorry

omit [IsManifold I ∞ M] in
theorem totalNabla0SFun_eval_section (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        (totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov α x)
        (Fin.cons (X x) slots) =
      Tensor0SSpace.eval
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α x)
        slots  := by sorry

def TotalNabla0SRealizes (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin s → TangentSpace I x),
      nablaAlpha x (Fin.cons (X x) slots) =
        nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α x slots

def TotalNablaRSRealizes (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (β : Tensor0SSpace r I x) (slots : Fin s → TangentSpace I x),
      nablaT x β (Fin.cons (X x) slots) =
        nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x β slots

omit [IsManifold I ∞ M] in
theorem TotalNabla0SRealizes.apply {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin s → TangentSpace I x) :
    nablaAlpha x (Fin.cons (X x) slots) =
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x slots  := by sorry

omit [IsManifold I ∞ M] in
theorem totalNabla0S_realizes (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α) :
    TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α
      (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg)  := by sorry

structure CanonicalSpatialDerivs0S {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) where
  nablaA : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (s + 1)
  nabla2A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (s + 2)
  first : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) s cov A nablaA
  second : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) (s + 1) cov nablaA nabla2A

theorem TotalNabla0SRealizes.eval_smooth_slots {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) :
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀)) =
      mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀)))  := by sorry

theorem TotalNabla0SRealizes.eval_C1_slots {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → (x : M) → TangentSpace I x)
    (x₀ : M)
    (hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀) :
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀)) =
      mvfderiv (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀)))  := by sorry

omit [IsManifold I ∞ M] in
theorem TotalNablaRSRealizes.apply {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {nablaT : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (h : TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (β : Tensor0SSpace r I x) (slots : Fin s → TangentSpace I x) :
    nablaT x β (Fin.cons (X x) slots) =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x β slots  := by sorry

noncomputable def totalNabla20S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg1 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α)
    (hreg2 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov
      (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg1)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + 1) + 1) :=
  totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1) cov
    (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α hreg1)
    hreg2

noncomputable def totalNabla20SSuccSucc (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg1 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α)
    (hreg2 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov
      (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg1)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
  totalNabla20S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov α hreg1 hreg2

inductive HigherCovDeriv0SRealizes
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    (k : ℕ) →
      Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (k + s) → Prop
  | zero :
      HigherCovDeriv0SRealizes cov α 0
        (by
          simpa :
            Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) (0 + s))
  | succ {k : ℕ}
      {αk : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (k + s)}
      {αk1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) ((k + s) + 1)}
      (hk : HigherCovDeriv0SRealizes cov α k αk)
      (hstep : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (k + s) cov αk αk1) :
      HigherCovDeriv0SRealizes cov α (k + 1)
        (by
          simpa [Nat.add_assoc, Nat.succ_add, Nat.add_comm, Nat.add_left_comm] using αk1 :
            Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) ((k + 1) + s))

inductive HigherCovDerivRSRealizes
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    (k : ℕ) →
      TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (k + s) → Prop
  | zero :
      HigherCovDerivRSRealizes cov T 0
        (by
          simpa :
            TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) r (0 + s))
  | succ {k : ℕ}
      {Tk : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (k + s)}
      {Tk1 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r ((k + s) + 1)}
      (hk : HigherCovDerivRSRealizes cov T k Tk)
      (hstep : TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r (k + s) cov Tk Tk1) :
      HigherCovDerivRSRealizes cov T (k + 1)
        (by
          simpa [Nat.add_assoc, Nat.succ_add, Nat.add_comm, Nat.add_left_comm] using Tk1 :
            TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) r ((k + 1) + s))

omit [IsManifold I ∞ M] in
theorem higherCovDeriv0SRealizes_two_apply {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {nabla2Alpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + 1) + 1)}
    (h2 : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (s + 1) cov nablaAlpha nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin (s + 1) → TangentSpace I x) :
    nabla2Alpha x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (s + 1) cov X nablaAlpha x slots  := by sorry

end

section RealLinearity


open Bundle Set IsManifold ContinuousLinearMap DifferentialGeometry.TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]

theorem nabla0SFun_sub_cov
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {s : ℕ}
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov' X α x) (fun a : Fin s => V a x) =
      -∑ a : Fin s,
        α x
          (Function.update (fun b : Fin s => V b x) a
            (((CovariantDerivative.difference cov cov' x) (V a x)) (X x)))  := by sorry

theorem nabla0SFun_sub_cov_two
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) :
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov' X α x)
        (fun q : Fin 2 => if q = 0 then Y x else Z x) =
      -((α x)
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference cov cov' x) (Y x)) (X x)
            else Z x) +
        (α x)
          (fun q : Fin 2 =>
            if q = 0 then Y x
            else ((CovariantDerivative.difference cov cov' x) (Z x)) (X x)))  := by sorry

theorem nabla0SFun_add [T2Space M] {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (α + β) x =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x +
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X β x  := by sorry

theorem nabla0SFun_smul [T2Space M] {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (c : Real)
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (c • α) x =
      c • nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x  := by sorry

theorem TotalNabla0SRealizes.add [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha nablaBeta :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (hβ : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov β nablaBeta) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov (α + β) (nablaAlpha + nablaBeta)  := by sorry

theorem TotalNabla0SRealizes.smul [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (c : Real)
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov (c • α) (c • nablaAlpha)  := by sorry

end RealLinearity

end Tensor0SBundle
end DifferentialGeometry

