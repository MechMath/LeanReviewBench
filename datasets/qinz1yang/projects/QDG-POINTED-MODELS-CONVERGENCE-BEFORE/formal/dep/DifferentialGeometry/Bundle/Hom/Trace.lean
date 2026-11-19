import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Trace

noncomputable section
open Bundle Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {M : Type*} [TopologicalSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]

theorem ContinuousWithinAt.trace_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z} {z₀ : Z}
    {A : ∀ z, V (b z) →L[𝕜] V (b z)}
    (hA : ContinuousWithinAt (fun z =>
      (TotalSpace.mk' (F →L[𝕜] F) (b z) (A z) :
        TotalSpace (F →L[𝕜] F) (fun x => V x →L[𝕜] V x))) s z₀) :
    ContinuousWithinAt (fun z => LinearMap.trace 𝕜 (V (b z)) (A z).toLinearMap) s z₀  := by sorry

theorem ContinuousOn.trace_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z}
    {A : ∀ z, V (b z) →L[𝕜] V (b z)}
    (hA : ContinuousOn (fun z =>
      (TotalSpace.mk' (F →L[𝕜] F) (b z) (A z) :
        TotalSpace (F →L[𝕜] F) (fun x => V x →L[𝕜] V x))) s) :
    ContinuousOn (fun z => LinearMap.trace 𝕜 (V (b z)) (A z).toLinearMap) s  := by sorry

end

open Bundle Filter in
open scoped Manifold ContDiff Topology in
theorem ContMDiffAt.trace_bundle
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] [VectorBundle 𝕜 F V]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    {n : ℕ∞ω} {b : P → M} {A : ∀ p : P, V (b p) →L[𝕜] V (b p)} {p : P}
    (hA : ContMDiffAt IP (I.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun q => (⟨b q, A q⟩ : TotalSpace (F →L[𝕜] F)
        (fun y : M => V y →L[𝕜] V y))) p) :
    ContMDiffAt IP 𝓘(𝕜) n
      (fun q => LinearMap.trace 𝕜 (V (b q)) (A q).toLinearMap) p  := by sorry

