import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section

open Function
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace HB X]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {n : WithTop ℕ∞}

lemma contMDiffAt_clm_of_pointwise
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun q => A q v) x) :
    ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x  := by sorry

lemma contMDiffWithinAt_clm_of_pointwise
    {A : X → (F₁ →L[𝕜] F₂)} {s : Set X} {x : X}
    (h : ∀ v, ContMDiffWithinAt IB 𝓘(𝕜, F₂) n (fun q => A q v) s x) :
    ContMDiffWithinAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A s x  := by sorry

