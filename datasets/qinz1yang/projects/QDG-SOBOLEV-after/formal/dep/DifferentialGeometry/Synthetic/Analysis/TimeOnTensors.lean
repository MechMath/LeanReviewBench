import dep.DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



set_option autoImplicit false
set_option linter.unusedSectionVars false
open BigOperators
open SyntheticTensor





section DtTensor

variable {R V : Type*} {A Time : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [CommRing A] [Algebra R A]


noncomputable def dt_tensor (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r s : ℕ} (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs)) : TensorData R V r s where
  toFun vs :=
    { toFun := fun αs => td.dt_apply (fun s => T s vs αs) t
      map_update_add' := by
        intro inst αs idx β₁ β₂
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        have h : (fun s => T s vs (Function.update αs idx (β₁ + β₂))) =
            (fun s => T s vs (Function.update αs idx β₁)) +
            (fun s => T s vs (Function.update αs idx β₂)) := by
          ext s; exact (T s vs).map_update_add αs idx β₁ β₂
        rw [h, td.dt_apply_add _ _ _
          (hT vs (Function.update αs idx β₁))
          (hT vs (Function.update αs idx β₂))]
      map_update_smul' := by
        intro inst αs idx c β
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        simp only [smul_eq_mul]
        have h : (fun s => T s vs (Function.update αs idx (c • β))) =
            (fun s => c * T s vs (Function.update αs idx β)) := by
          ext s
          change T s vs (Function.update αs idx (c • β)) = c * T s vs (Function.update αs idx β)
          have := (T s vs).map_update_smul αs idx c β; rwa [smul_eq_mul] at this
        rw [h]
        exact td.dt_apply_const_mul c _ t (hT vs (Function.update αs idx β)) }
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    have h : (fun s => T s (Function.update vs idx (v₁ + v₂)) αs) =
        (fun s => T s (Function.update vs idx v₁) αs) +
        (fun s => T s (Function.update vs idx v₂) αs) := by
      ext s; exact congr_arg (· αs) ((T s).map_update_add vs idx v₁ v₂)
    rw [h, td.dt_apply_add _ _ _
      (hT (Function.update vs idx v₁) αs)
      (hT (Function.update vs idx v₂) αs)]
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    have h : (fun s => T s (Function.update vs idx (c • v)) αs) =
        (fun s => c * T s (Function.update vs idx v) αs) := by
      ext s; change T s (Function.update vs idx (c • v)) αs = c * T s (Function.update vs idx v) αs
      have := congr_arg (· αs) ((T s).map_update_smul vs idx c v)
      simp only [MultilinearMap.smul_apply, smul_eq_mul] at this; exact this
    rw [h]
    exact td.dt_apply_const_mul c _ t (hT (Function.update vs idx v) αs)






theorem dt_tensor_eval (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r s : ℕ} (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs)) (vs αs) :
    dt_tensor td t T hT vs αs = td.dt_apply (fun s => T s vs αs) t  := by sorry

theorem dt_tensor_const (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r s : ℕ} (T : TensorData R V r s) :
    dt_tensor td t (fun _ => T)
      (fun vs αs => td.isSmoothFam_const (T vs αs)) = 0  := by sorry

theorem dt_tensor_add (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r s : ℕ} (T₁ T₂ : Time → TensorData R V r s)
    (hT₁ : ∀ vs αs, td.isSmoothFam (fun τ => T₁ τ vs αs))
    (hT₂ : ∀ vs αs, td.isSmoothFam (fun τ => T₂ τ vs αs)) :
    dt_tensor td t (fun s => T₁ s + T₂ s)
      (fun vs αs => td.isSmoothFam_add _ _ (hT₁ vs αs) (hT₂ vs αs)) =
    dt_tensor td t T₁ hT₁ + dt_tensor td t T₂ hT₂  := by sorry

theorem dt_tensor_neg (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r s : ℕ} (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs)) :
    dt_tensor td t (fun s => -T s)
      (fun vs αs => td.isSmoothFam_neg _ (hT vs αs)) = -dt_tensor td t T hT  := by sorry

theorem dt_tensor_sub (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r s : ℕ} (T₁ T₂ : Time → TensorData R V r s)
    (hT₁ : ∀ vs αs, td.isSmoothFam (fun τ => T₁ τ vs αs))
    (hT₂ : ∀ vs αs, td.isSmoothFam (fun τ => T₂ τ vs αs)) :
    dt_tensor td t (fun s => T₁ s - T₂ s)
      (fun vs αs => td.isSmoothFam_sub _ _ (hT₁ vs αs) (hT₂ vs αs)) =
    dt_tensor td t T₁ hT₁ - dt_tensor td t T₂ hT₂  := by sorry

theorem dt_tensor_smul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r s : ℕ} (f : Time → R) (T : Time → TensorData R V r s)
    (hf : td.isSmoothFam f)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (vs αs) :
    dt_tensor td t (fun s => f s • T s)
      (fun vs αs => td.isSmoothFam_mul _ _ hf (hT vs αs)) vs αs =
    td.dt_apply f t * (T t vs αs) + f t * dt_tensor td t T hT vs αs  := by sorry

theorem dt_tensor_smul_const (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r s : ℕ} (c : R) (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs)) :
    dt_tensor td t (fun s => c • T s)
      (fun vs αs => td.isSmoothFam_const_mul c _ (hT vs αs)) =
    c • dt_tensor td t T hT  := by sorry

theorem dt_tensor_prod (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : Time → TensorData R V r₁ s₁) (T₂ : Time → TensorData R V r₂ s₂)
    (hT₁ : ∀ vs αs, td.isSmoothFam (fun τ => T₁ τ vs αs))
    (hT₂ : ∀ vs αs, td.isSmoothFam (fun τ => T₂ τ vs αs))
    (hT_prod : ∀ vs αs, td.isSmoothFam
      (fun τ => tensor_prod (T₁ τ) (T₂ τ) vs αs)) :
    dt_tensor td t (fun s => tensor_prod (T₁ s) (T₂ s)) hT_prod =
    tensor_prod (dt_tensor td t T₁ hT₁) (T₂ t) +
    tensor_prod (T₁ t) (dt_tensor td t T₂ hT₂)  := by sorry

theorem dt_tensor_swap (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) {r s : ℕ} (i j : Fin s)
    (T : Time → TensorData R V r s)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (hT_swap : ∀ vs αs, td.isSmoothFam (fun τ => swap_covariant i j (T τ) vs αs))
    (vs αs) :
    dt_tensor td t (fun s => swap_covariant i j (T s)) hT_swap vs αs =
    swap_covariant i j (dt_tensor td t T hT) vs αs  := by sorry

theorem dt_tr (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (atr : AbstractTrace R V)
    (h_tt : TimeTrComm atr td)
    (L : Time → V →ₗ[R] V) (dL : V →ₗ[R] V) (t : Time)
    (h_αLv_smooth : ∀ (v : V) (α : V →ₗ[R] R),
      td.isSmoothFam (fun s => α (L s v)))
    (h_trL_smooth : td.isSmoothFam (fun s => atr.tr (L s)))
    (h_char : ∀ (v : V) (α : V →ₗ[R] R),
      α (dL v) = td.dt_apply (fun s => α (L s v)) t) :
    td.dt_apply (fun s => atr.tr (L s)) t = atr.tr dL  := by sorry

end DtTensor
