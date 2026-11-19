





import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

noncomputable section Comp

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι : Type*} [Finite ι]

theorem compContinuousMultilinearMapL_diag_continuous :
    Continuous (fun p : M →L[𝕜] M' ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
        ContinuousMultilinearMap 𝕜 (fun _ ↦ M') N →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ M) N))
   := by sorry

end ContinuousLinearMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Finite ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous :
  Continuous (fun p : F₁ →L[𝕜] F₁ ↦
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂))
   := by sorry

end Continuous

section Smooth
variable {𝕜 ι F₁ F₂} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff :
  ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂))
   := by sorry

theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff_of_space
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] :
    ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁' ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
        ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁') F₂ →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂))  := by sorry

end Smooth

end Comp

