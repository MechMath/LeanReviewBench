import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Model.Tensor0S
open DifferentialGeometry.Tensor.Multilinear

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

omit [CompleteSpace 𝕜] in
theorem fderivWithin_tensorRSModel_eval_slots {r s : ℕ}
    (T : E → TensorRSModel r s 𝕜 E)
    (β : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r)
    (V : Fin s → E → E)
    (u : Set E) (y Xy : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hβ : DifferentiableWithinAt 𝕜 β u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 (fun z : E => (T z (β z)) (fun a : Fin s => V a z)) u y Xy =
      ((fderivWithin 𝕜 T u y Xy) (β y)) (fun a : Fin s => V a y) +
        (T y (fderivWithin 𝕜 β u y Xy)) (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          (T y (β y)) (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy))  := by sorry

theorem covariantDeriv_tensorRSModelWithin_eval_derivation {r s : ℕ}
    (T : E → TensorRSModel r s 𝕜 E)
    (β : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r)
    (V : Fin s → E → E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (u : Set E) (y : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hβ : DifferentiableWithinAt 𝕜 β u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    (covariantDerivTensorRSModelWithin (𝕜 := 𝕜) (E := E)
        r s X ΓX T u y (β y)) (fun a : Fin s => V a y)
      =
        fderivWithin 𝕜
          (fun z : E => (T z (β z)) (fun a : Fin s => V a z))
          u y (X y)
        - (T y
          (covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E)
            r X ΓX β u y))
          (fun a : Fin s => V a y)
        - ∑ a : Fin s,
          (T y (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y) + ΓX y (V a y)))  := by sorry

section ChristoffelModelRS

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_eval_update_basis_sum_modelRS {d s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (v : Fin s → E) (i : Fin s) (w : E) :
    α (Function.update v i w) =
      ∑ k : Fin d, basis.coord k w *
        α (Function.update v i (basis k))  := by sorry

private theorem continuousMultilinearMap_basis_apply_basis {d s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (upper lower : Fin s → Fin d) :
    ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis s) upper)
        (fun b : Fin s => basis (lower b)) =
      if upper = lower then 1 else 0  := by sorry

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
private theorem basis_coord_update_sum_comm {d r : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (upper lower : Fin r → Fin d)
    (a : Fin r) :
    (∑ k : Fin d,
        basis.coord k (ΓX (basis (lower a))) *
          (if upper = Function.update lower a k then (1 : 𝕜) else 0)) =
      ∑ k : Fin d,
        basis.coord (upper a) (ΓX (basis k)) *
          (if Function.update upper a k = lower then (1 : 𝕜) else 0)  := by sorry

theorem lieDeriv_correctionL_apply_basis_slots_expanded {d s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (lower : Fin s → Fin d) :
    ((lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX α)
        (fun b : Fin s => basis (lower b))) =
      ∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX (lower b) k *
          α (Function.update
            (fun c : Fin s => basis (lower c))
            b
            (basis k))  := by sorry

theorem lieDeriv_correctionL_apply_basisTensor0S {d r : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (upper : Fin r → Fin d) :
    lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r ΓX
      ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper)
    =
      ∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) •
          ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r)
            (Function.update upper a k))  := by sorry

theorem covariantDeriv_tensorRSModelAt_apply_basis_slots {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (dT_X : TensorRSModel r s 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (upper : Fin r → Fin d)
    (lower : Fin s → Fin d) :
    (covariantDerivTensorRSModelAt
        (𝕜 := 𝕜) (E := E) r s dT_X ΓX T
        ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper))
      (fun b : Fin s => basis (lower b))
    =
      (dT_X
        ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper))
        (fun b : Fin s => basis (lower b))
      +
      ∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) *
          (T
            ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))
      -
      ∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX (lower b) k *
          (T
            ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k))  := by sorry

theorem covDerivRS_sub_apply {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (dT_X : TensorRSModel r s 𝕜 E)
    (ΓX ΓX' : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (upper : Fin r → Fin d)
    (lower : Fin s → Fin d) :
    ((covariantDerivTensorRSModelAt
          (𝕜 := 𝕜) (E := E) r s dT_X ΓX T -
        covariantDerivTensorRSModelAt
          (𝕜 := 𝕜) (E := E) r s dT_X ΓX' T)
        ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper))
      (fun b : Fin s => basis (lower b))
    =
      (((∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) *
          (T
            ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))) -
        (∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX' k (upper a) *
          (T
            ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))))
      -
      ((∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX (lower b) k *
          (T
            ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k))) -
        (∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX' (lower b) k *
          (T
            ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k)))))  := by sorry

theorem covariantDeriv_tensorRSModelWithin_apply_basis_slots {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (X : E → E)
    (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E)
    (u : Set E)
    (x : E)
    (upper : Fin r → Fin d)
    (lower : Fin s → Fin d) :
    (covariantDerivTensorRSModelWithin
        (𝕜 := 𝕜) (E := E) r s X ΓX T u x
        ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper))
      (fun b : Fin s => basis (lower b))
    =
      (fderivWithin 𝕜 T u x (X x)
        ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper))
        (fun b : Fin s => basis (lower b))
      +
      ∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis (ΓX x) k (upper a) *
          (T x
            ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))
      -
      ∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis (ΓX x) (lower b) k *
          (T x
            ((continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k))  := by sorry

end ChristoffelModelRS

end ModelCovariantDerivative

end

end TensorLieDeriv
end DifferentialGeometry

