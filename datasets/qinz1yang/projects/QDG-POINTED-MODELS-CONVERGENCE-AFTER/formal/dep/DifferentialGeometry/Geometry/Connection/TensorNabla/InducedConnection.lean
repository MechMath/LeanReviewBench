import dep.DifferentialGeometry.Geometry.LieDerivative.Tensor
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic


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

def covariantDerivTensor0SModelAt (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  dα_X - lieDerivCorrection s ΓX α

omit [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_tensor0SModelAt_apply (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α =
      dα_X - lieDerivCorrection s ΓX α  := by sorry

def covariantDerivTensor0SModel (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderiv 𝕜 α x (X x)) (ΓX x) (α x)

def covariantDerivTensor0SModelWithin (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x)

def covariantDerivTensorRSModelAt (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    TensorRSModel r s 𝕜 E :=
  dT_X
    - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
    + T.comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r ΓX)

@[simp] theorem covariantDeriv_tensorRSModelAt_apply (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    covariantDerivTensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T =
      dT_X
        - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
        + T.comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r ΓX)  := by sorry

theorem covariantDeriv_tensorRSModelAt_eval (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) r) (v : Fin s → E) :
    (covariantDerivTensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T β) v =
      (dT_X β) v -
        ((lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX) (T β)) v +
        (T ((lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r ΓX) β)) v  := by sorry

section ChristoffelModel

variable {Idx : Type*} [Fintype Idx]

def connectionEndomorphismCoeff
    (basis : Module.Basis Idx 𝕜 E) (ΓX : E →L[𝕜] E)
    (j k : Idx) : 𝕜 :=
  basis.coord k (ΓX (basis j))

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_eval_update_basis_sum {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (v : Fin s → E) (i : Fin s) (w : E) :
    α (Function.update v i w) =
      ∑ k : Idx, basis.coord k w *
        α (Function.update v i (basis k))  := by sorry

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_one_eval_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 1) (v : E) :
    α (fun _ : Fin 1 => v) =
      ∑ k : Idx, basis.coord k v * α (fun _ : Fin 1 => basis k)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_two_eval_first_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k v *
        α (fun q : Fin 2 => if q = 0 then basis k else w)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_two_eval_second_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k w *
        α (fun q : Fin 2 => if q = 0 then v else basis k)  := by sorry

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelAt_apply_basis_slots {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → Idx) :
    covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α
        (fun a : Fin s => basis (slots a)) =
      dα_X (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis ΓX (slots a) k *
            α (Function.update (fun b : Fin s => basis (slots b)) a (basis k))  := by sorry

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_apply_basis_slots {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (u : Set E) (x : E) (slots : Fin s → Idx) :
    covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E) s X ΓX α u x
        (fun a : Fin s => basis (slots a)) =
      fderivWithin 𝕜 α u x (X x) (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX x) (slots a) k *
            α x (Function.update (fun b : Fin s => basis (slots b)) a (basis k))  := by sorry

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelAt_one_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (j : Idx) :
    covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) 1 dα_X ΓX α
        (fun _ : Fin 1 => basis j) =
      dα_X (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX j k *
          α (fun _ : Fin 1 => basis k)  := by sorry

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelAt_two_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (dA_X : Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (ΓX : E →L[𝕜] E)
    (A : Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (j l : Idx) :
    covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) 2 dA_X ΓX A
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      dA_X (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX j k *
          A (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX l k *
          A (fun q : Fin 2 => if q = 0 then basis j else basis k)  := by sorry

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_one_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (u : Set E) (x : E) (j : Idx) :
    covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E) 1 X ΓX α u x
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜 α u x (X x) (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          α x (fun _ : Fin 1 => basis k)  := by sorry

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_two_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (A : E → Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (u : Set E) (x : E) (j l : Idx) :
    covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E) 2 X ΓX A u x
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜 A u x (X x)
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          A x (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) l k *
          A x (fun q : Fin 2 => if q = 0 then basis j else basis k)  := by sorry

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_one_apply_basis_clm
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => E) 𝕜)
    (u : Set E) (x : E) (j : Idx) :
    covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E) 1 X ΓX α u x
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜 α u x (X x) (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          α x (fun _ : Fin 1 => basis k)  := by sorry

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_two_apply_basis_clm
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (A : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => E) 𝕜)
    (u : Set E) (x : E) (j l : Idx) :
    covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E) 2 X ΓX A u x
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜 A u x (X x)
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          A x (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) l k *
          A x (fun q : Fin 2 => if q = 0 then basis j else basis k)  := by sorry

end ChristoffelModel

def covariantDerivTensorRSModel (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDerivTensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderiv 𝕜 T x (X x)) (ΓX x) (T x)

def covariantDerivTensorRSModelWithin (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (u : Set E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDerivTensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderivWithin 𝕜 T u x (X x)) (ΓX x) (T x)

omit [CompleteSpace 𝕜] in
lemma covariantSlotCorrection_modelProduct (s q : ℕ) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) q) :
    lieDerivCorrection (s + q) ΓX
        (Bundle.continuousMultilinearMap.modelProduct s q α β) =
      Bundle.continuousMultilinearMap.modelProduct s q
          (lieDerivCorrection s ΓX α) β +
        Bundle.continuousMultilinearMap.modelProduct s q
          α (lieDerivCorrection q ΓX β)  := by sorry

end ModelCovariantDerivative

section TangentCovariantDerivative

variable [IsManifold I 1 M]

def covariantDerivVectorField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    TangentSpace I x :=
  cov Y x (X x)

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_vectorField_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    covariantDerivVectorField (I := I) cov X Y x = cov Y x (X x)  := by sorry

noncomputable def tangentConstInChart (x₀ : M) (v : E) (p : M) :
    TangentSpace I p :=
  (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma tangentConstInChart_apply (x₀ : M) (v : E) (p : M) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v p =
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v  := by sorry

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma tangentConstInChart_add (x₀ : M) (v w : E) :
    (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
      (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
        tangentConstInChart x₀ w  := by sorry

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma tangentConstInChart_smul (x₀ : M) (a : 𝕜) (v : E) :
    (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
      a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)  := by sorry

section ConnectionEndomorphism

variable [IsManifold I 2 M]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma mdifferentiableAt_tangentConstInChart_of_mem
    {x₀ p : M} (v : E)
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p  := by sorry

noncomputable def connectionEndomorphismInChart
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) (y : E) :
    E →L[𝕜] E := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let p := (extChartAt I x₀).symm y
  refine LinearMap.toContinuousLinearMap ?_
  refine
    { toFun := fun v =>
        if y ∈ (extChartAt I x₀).target then
          e.continuousLinearMapAt 𝕜 p
            ((cov (tangentConstInChart x₀ v) p) (X p))
        else
          0
      map_add' := ?_
      map_smul' := ?_ }
  · intro v w
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hw : MDiffAt
          (T% (tangentConstInChart x₀ w : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) w hp_base
      have hsection :
          (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
            (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w :=
        tangentConstInChart_add x₀ v w
      have hcov :
          cov ((tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w) p =
            cov (tangentConstInChart x₀ v) p +
              cov (tangentConstInChart x₀ w) p :=
        cov.isCovariantDerivativeOnUniv.add hv hw
      rw [ite_eq_left hy, ite_eq_left hy, ite_eq_left hy]
      rw [hsection, hcov]
      simp [map_add]
    · rw [ite_eq_right hy, ite_eq_right hy, ite_eq_right hy]
      simp
  · intro a v
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hsection :
          (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
            a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) :=
        tangentConstInChart_smul x₀ a v
      have hcov :
          cov (a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p =
            a • cov (tangentConstInChart x₀ v) p :=
        cov.isCovariantDerivativeOnUniv.smul_const a hv
      rw [ite_eq_left hy, ite_eq_left hy]
      rw [hsection, hcov]
      simp [map_smul]
    · rw [ite_eq_right hy, ite_eq_right hy]
      simp

lemma connectionEndomorphismInChart_apply_of_mem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v : E) :
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀ y v =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v)
          ((extChartAt I x₀).symm y))
          (X ((extChartAt I x₀).symm y)))  := by sorry

lemma connectionEndomorphismInChart_apply_of_notMem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) {y : E}
    (hy : y ∉ (extChartAt I x₀).target) (v : E) :
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀ y v = 0  := by sorry

end ConnectionEndomorphism

end TangentCovariantDerivative

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

noncomputable def tensor0SModelAt (s : ℕ) (x₀ x : M)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (fun p : M => Tensor0SSpace s I p) x₀)
    ⟨x, A⟩).2

omit [CompleteSpace 𝕜] in
theorem tensor0SModelAt_trivializationAt_symm (s : ℕ) (x₀ : M)
    (T : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
          (fun p : M => Tensor0SSpace s I p) x₀).symm
          x₀ T) = T  := by sorry

noncomputable def tensor0SModelInChart (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (y : E) : Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s x₀ ((extChartAt I x₀).symm y) (A ((extChartAt I x₀).symm y))

private noncomputable def vectorFieldModelInChart (x₀ : M)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) (y : E) : E :=
  tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) y
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      X (range I) y)

omit [IsManifold I n M] [CompleteSpace 𝕜] [IsManifold I (n + 1) M] in
theorem tensor0SModelInChart_contMDiffWithinAt (s : ℕ) (x₀ : M)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, Tensor0SModel (𝕜 := 𝕜) (E := E) s) n
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s x₀ (fun x => α x))
      (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
      (extChartAt I x₀ x₀)  := by sorry

noncomputable def mcovariantDerivTensor0SWithin (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ := by
  let X' : E → E := vectorFieldModelInChart (I := I) (n := n) x₀ X
  let α' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s x₀ (fun x => α x)
  exact
    (trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (fun p : M => Tensor0SSpace s I p) x₀).symm
        x₀
      (covariantDerivTensor0SModelWithin s X' ΓX α'
        ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
        (extChartAt I x₀ x₀))

omit [IsManifold I n M] [IsManifold I (n + 1) M] [CompleteSpace 𝕜] in
theorem mcovariantDeriv_tensor0SWithin_one_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) 1)
    (u : Set M) (x₀ : M) (j : Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 x₀ x₀
        (mcovariantDerivTensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) 1 X ΓX α u x₀))
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) 1 x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (tangentSpaceModelContinuousLinearEquiv (extChartAt I x₀ x₀)
            (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
              X (range I) (extChartAt I x₀ x₀)))
          (fun _ : Fin 1 => basis j) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) j k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              1 x₀ x₀ (α x₀)) (fun _ : Fin 1 => basis k)  := by sorry

omit [IsManifold I n M] [IsManifold I (n + 1) M] [CompleteSpace 𝕜] in
theorem mcovariantDeriv_tensor0SWithin_two_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) 2)
    (u : Set M) (x₀ : M) (j l : Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        2 x₀ x₀
        (mcovariantDerivTensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) 2 X ΓX A u x₀))
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) 2 x₀ (fun x => A x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (tangentSpaceModelContinuousLinearEquiv (extChartAt I x₀ x₀)
            (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
              X (range I) (extChartAt I x₀ x₀)))
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) j k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              2 x₀ x₀ (A x₀)) (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) l k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              2 x₀ x₀ (A x₀)) (fun q : Fin 2 => if q = 0 then basis j else basis k)  := by sorry

omit [IsManifold I n M] [IsManifold I (n + 1) M] [CompleteSpace 𝕜] in
theorem mcovariantDeriv_tensor0SWithin_apply_basis_slots
    {Idx : Type*} [Fintype Idx] {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (u : Set M) (x₀ : M) (slots : Fin s → Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        (mcovariantDerivTensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) s X ΓX α u x₀))
        (fun a : Fin s => basis (slots a)) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) s x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (tangentSpaceModelContinuousLinearEquiv (extChartAt I x₀ x₀)
            (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
              X (range I) (extChartAt I x₀ x₀)))
          (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) (slots a) k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              s x₀ x₀ (α x₀))
              (Function.update (fun b : Fin s => basis (slots b)) a (basis k))  := by sorry

noncomputable def mcovariantDerivTensor0S (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDerivTensor0SWithin (n := n) s X ΓX α univ x₀

noncomputable def mcovariantDerivTensorRSWithin (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ := by
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  let X' : E → E := vectorFieldModelInChart (I := I) (n := n) x₀ X
  let T' : E → TensorRSModel r s 𝕜 E :=
    fun y =>
      ((trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀)
        ⟨(extChartAt I x₀).symm y, T.toFun ((extChartAt I x₀).symm y)⟩).2
  exact
    (trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀).symm x₀
      (covariantDerivTensorRSModelWithin r s X' ΓX T'
        ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
        (extChartAt I x₀ x₀))

noncomputable def mcovariantDerivTensorRS (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDerivTensorRSWithin (n := n) r s X ΓX T univ x₀

section ExtractedConnection

variable [IsManifold I 2 M]

noncomputable def mcovariantDerivTensor0SWithinFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDerivTensor0SWithin (n := n) s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) α u x₀

noncomputable def mcovariantDerivTensor0SFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDerivTensor0SWithinFromConnection (n := n) s cov X α univ x₀

noncomputable def mcovariantDerivTensorRSWithinFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDerivTensorRSWithin (n := n) r s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) T u x₀

noncomputable def mcovariantDerivTensorRSFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDerivTensorRSWithinFromConnection (n := n) r s cov X T univ x₀

end ExtractedConnection

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv

namespace Tensor0SBundle

noncomputable section


open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Function
    DifferentialGeometry.TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace 𝕜]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable {n : WithTop ℕ∞}
variable [IsManifold I n M]
variable [IsManifold I (n + 1) M]

noncomputable def nabla0SFun (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x : M) : Tensor0SSpace s I x :=
  TensorLieDeriv.mcovariantDerivTensor0SFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := n) s cov X α x

noncomputable def nablaRSFun (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (x : M) : TensorRSSpace r s I x :=
  TensorLieDeriv.mcovariantDerivTensorRSFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := n) r s cov X T x

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
@[simp] theorem nabla0SFun_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x : M) :
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x =
      TensorLieDeriv.mcovariantDerivTensor0SFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := n) s cov X α x  := by sorry

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
@[simp] theorem nablaRSFun_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (x : M) :
    nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x =
      TensorLieDeriv.mcovariantDerivTensorRSFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := n) r s cov X T x  := by sorry

abbrev Nabla0SRegular (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s) : Prop :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) n
    (fun x : M =>
      (⟨x, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x⟩ :
        TotalSpace (Tensor0SModel s 𝕜 E) (fun x : M => Tensor0SSpace s I x)))

abbrev NablaRSRegular (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s) : Prop :=
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiff I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E)) n
    (fun x : M =>
      (⟨x, nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x⟩ :
        TotalSpace (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)))

noncomputable def nabla0S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ⟨nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α, hreg⟩

noncomputable def nablaRS (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s :=
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ⟨nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T, hreg⟩

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
@[simp] theorem nabla0S_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α)
    (x : M) :
    nabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α hreg x =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x  := by sorry

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
@[simp] theorem nablaRS_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T)
    (x : M) :
    nablaRS (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T hreg x =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x  := by sorry

end

end Tensor0SBundle
end DifferentialGeometry

