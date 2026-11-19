





import dep.DifferentialGeometry.Tensor.Multilinear.Composition
import dep.DifferentialGeometry.Analysis.Calculus.AnalyticTransfer
import dep.DifferentialGeometry.Tensor.Multilinear.Smoothness.LinearIsometry
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

open ContinuousAlternatingMap

noncomputable section Comp

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' := by
  let F₁ : MultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') := MultilinearMap.mk
    (toFun := fun v => (f (g v)).compContinuousAlternatingMap h)
    (map_update_add' := fun m i x y => by
      simp only [ContinuousAlternatingMap.map_update_add, map_add]
      congr)
    (map_update_smul' := fun m i c x => by
      rw [ContinuousAlternatingMap.map_update_smul, ContinuousLinearMap.map_smul]
      congr)
  let F₂ : ContinuousMultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') :=
    F₁.mkContinuous (‖f‖ * ‖g‖ * ‖h‖) (H := by
      intro m
      unfold F₁
      simp only [MultilinearMap.coe_mk]
      apply ContinuousAlternatingMap.opNorm_le_bound
      · positivity
      intro m'
      simp only [compContinuousAlternatingMap_coe, Function.comp_apply]
      calc
        ‖(f (g m)) (h m')‖ ≤ ‖f (g m)‖ * ‖h m'‖ := ContinuousLinearMap.le_opNorm (f (g m)) (h m')
        _ ≤ ‖f (g m)‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_left
          · exact ContinuousAlternatingMap.le_opNorm h m'
          positivity
        _ ≤ ‖f‖ * ‖g m‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · exact ContinuousLinearMap.le_opNorm f (g m)
          positivity
        _ ≤ ‖f‖ * (‖g‖ * ∏ i, ‖m i‖) * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left
            · exact ContinuousAlternatingMap.le_opNorm g m
            positivity
          positivity
        _ = (‖f‖ * ‖g‖ * ‖h‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)
  exact ContinuousAlternatingMap.mk F₂ (map_eq_zero_of_eq' := by
    intro v i j h₁ h₂
    simp only [MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
      MultilinearMap.coe_mkContinuous, MultilinearMap.coe_mk, F₂, F₁]
    have : g v = 0 := g.map_eq_zero_of_eq' v i j h₁ h₂
    rw [this, ContinuousLinearMap.map_zero]
    ext v'
    rfl)

theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m')  := by sorry

theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m')  := by sorry

theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m')  := by sorry

noncomputable def _root_.LinearIsometry.compLeft {𝕜 : Type*} {𝕜₂ : Type*}
    {𝕜₃ : Type*} (E : Type*) {F : Type*} {G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] (σ₁₂ : 𝕜 →+* 𝕜₂) {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃]
    [RingHomIsometric σ₁₃] (f : F →ₛₗᵢ[σ₂₃] G) :
    (E →SL[σ₁₂] F) →ₛₗᵢ[σ₂₃] (E →SL[σ₁₃] G) :=
  { ContinuousLinearMap.compSL _ _ _ _ _ f.toContinuousLinearMap with
    norm_map' := fun _ ↦ f.norm_toContinuousLinearMap_comp }

omit [Fintype ι] in
theorem compContinuousAlternatingMapCLM_cont [Finite ι] :
    Continuous (ContinuousAlternatingMap.compContinuousLinearMapCLM :
    (M →L[𝕜] M') → (M' [⋀^ι]→L[𝕜] N) →L[𝕜] (M [⋀^ι]→L[𝕜] N))  := by sorry

end ContinuousLinearMap

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι ι' : Type*}
variable
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  [Fintype ι] [Fintype ι']

def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' :=
  f.compContinuousAlternatingMap₂ g h

theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m')  := by sorry

theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m')  := by sorry

theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m')  := by sorry

omit [Fintype ι] in
theorem compContinuousLinearMap_compContinuousLinearMap
    {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    (L : E [⋀^ι]→L[𝕜] N) (A : E' →L[𝕜] E) (B : E'' →L[𝕜] E') :
    (L.compContinuousLinearMap A).compContinuousLinearMap B =
      L.compContinuousLinearMap (A ∘L B)  := by sorry

omit [Fintype ι] in
theorem compContinuousLinearMap_id {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (L : E [⋀^ι]→L[𝕜] N) :
    L.compContinuousLinearMap (ContinuousLinearMap.id 𝕜 E) = L  := by sorry

omit [Fintype ι] in
theorem compContinuousLinearMap_add {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (L₁ L₂ : E [⋀^ι]→L[𝕜] N)
    (A : E' →L[𝕜] E) :
    (L₁ + L₂).compContinuousLinearMap A =
      L₁.compContinuousLinearMap A + L₂.compContinuousLinearMap A  := by sorry

omit [Fintype ι] in
theorem compContinuousLinearMap_smul {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (c : 𝕜) (L : E [⋀^ι]→L[𝕜] N)
    (A : E' →L[𝕜] E) :
    (c • L).compContinuousLinearMap A = c • L.compContinuousLinearMap A  := by sorry

omit [Fintype ι] in
theorem compContinuousLinearMap_zero {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (A : E' →L[𝕜] E) :
    (0 : E [⋀^ι]→L[𝕜] N).compContinuousLinearMap A = 0  := by sorry

end ContinuousAlternatingMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Finite ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

theorem ContinuousAlternatingMap.compContinuousLinearMapL_continuous :
    Continuous (fun p : F₁ →L[𝕜] F₁ ↦
    (ContinuousAlternatingMap.compContinuousLinearMapCLM p :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))  := by sorry

end Continuous

section Smooth
variable {𝕜 ι F₁ F₂} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

open scoped Bundle Manifold

omit [CharZero 𝕜] in
private theorem norm_alternatization_le (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) :
    ‖ContinuousMultilinearMap.alternatization f‖ ≤
      (Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖  := by sorry

noncomputable def ContinuousMultilinearMap.alternatizationCLM : (ContinuousMultilinearMap 𝕜
    (fun _ : ι => F₁) F₂) →L[𝕜]
    (F₁ [⋀^ι]→L[𝕜] F₂) :=
  LinearMap.mkContinuous
    { toFun := fun f => (↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹ •
        ContinuousMultilinearMap.alternatization f
      map_add' := by
        intro f g
        ext v
        rw [show ContinuousMultilinearMap.alternatization (f + g) =
            ContinuousMultilinearMap.alternatization f +
              ContinuousMultilinearMap.alternatization g from
          (ContinuousMultilinearMap.alternatization.map_add f g)]
        rw [smul_add]
      map_smul' := by
        intro c f
        have hlin : ContinuousMultilinearMap.alternatization (c • f) =
            c • ContinuousMultilinearMap.alternatization f := by
          ext v
          rw [ContinuousMultilinearMap.alternatization_apply_apply]
          simp only [_root_.smul_apply]
          rw [ContinuousAlternatingMap.smul_apply,
            ContinuousMultilinearMap.alternatization_apply_apply,
            Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
        ext v
        simp only [ContinuousAlternatingMap.smul_apply, hlin]
        exact smul_comm ((↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹) c
          (ContinuousMultilinearMap.alternatization f v) }
    (‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ * Fintype.card (Equiv.Perm ι))
    (by
      intro f
      calc
        ‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹ • ContinuousMultilinearMap.alternatization f‖
            ≤ ‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ *
                ‖ContinuousMultilinearMap.alternatization f‖ :=
              norm_smul_le (r := (↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹)
                (x := ContinuousMultilinearMap.alternatization f)
        _ ≤ ‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ *
                ((Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖) := by
          exact mul_le_mul_of_nonneg_left (norm_alternatization_le f) (norm_nonneg _)
        _ = (‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ * Fintype.card (Equiv.Perm ι)) * ‖f‖ := by
          ring)

theorem ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap
    (L : F₁ [⋀^ι]→L[𝕜] F₂) :
    ContinuousMultilinearMap.alternatizationCLM
      (ContinuousAlternatingMap.toContinuousMultilinearMap L) = L  := by sorry

omit [CharZero 𝕜] in
theorem ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁']
    (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)
    (A : F₁' →L[𝕜] F₁) :
    ContinuousMultilinearMap.alternatizationCLM
        (f.compContinuousLinearMap (fun _ => A)) =
      (ContinuousMultilinearMap.alternatizationCLM f).compContinuousLinearMap A  := by sorry

omit [DecidableEq ι] in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff :
    ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ =>
      (compContinuousLinearMapCLM p : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜]
        (F₁ [⋀^ι]→L[𝕜] F₂)))  := by sorry

omit [DecidableEq ι] in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff :
    let F : (F₁ →L[𝕜] F₁) → (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁))) (𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤ F  := by sorry

omit [DecidableEq ι] in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] :
    ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁' =>
      (compContinuousLinearMapCLM p : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜]
        (F₁ [⋀^ι]→L[𝕜] F₂)))  := by sorry

omit [DecidableEq ι] in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] :
    let F : (F₁ →L[𝕜] F₁') → (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁'))) (𝓘(𝕜,
      ((F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤ F  := by sorry

end Smooth

section Smooth
variable {ι F₁ F₂} [Fintype ι]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

open scoped Bundle Manifold

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_real :
    ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁ =>
      (compContinuousLinearMapCLM p : (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        (F₁ [⋀^ι]→L[ℝ] F₂)))  := by sorry

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_real :
    let F : (F₁ →L[ℝ] F₁) → (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(ℝ, (F₁ →L[ℝ] F₁))) (𝓘(ℝ, ((F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)))) ⊤ F  := by sorry

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] :
    ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁' =>
      (compContinuousLinearMapCLM p : (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        (F₁ [⋀^ι]→L[ℝ] F₂)))  := by sorry

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] :
    let F : (F₁ →L[ℝ] F₁') → (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(ℝ, (F₁ →L[ℝ] F₁'))) (𝓘(ℝ,
      ((F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)))) ⊤ F  := by sorry

end Smooth

end Comp

