import dep.DifferentialGeometry.Bundle.Equiv
import dep.DifferentialGeometry.Bundle.Hom.Trace
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import dep.DifferentialGeometry.Bundle.Zero
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import dep.DifferentialGeometry.Bundle.Frame
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contMDiff_continuousLinearMap_section_of_apply
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    [T2Space M]
    (φ : ∀ x : M, TangentSpace I x →L[ℝ] V₂ x)
    (h : ∀ (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
        (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F₂)
        (E := fun x : M => TangentSpace I x →L[ℝ] V₂ x) x (φ x))  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem contMDiffAt_linearMap_trace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    {n : ℕ∞ω} (A : ∀ x : M, V x →L[ℝ] V x) {x : M}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun x : M => (⟨x, A x⟩ : TotalSpace (F →L[ℝ] F)
        (fun y : M => V y →L[ℝ] V y))) x) :
    ContMDiffAt I 𝓘(ℝ) n
      (fun y : M => LinearMap.trace ℝ (V y) (A y).toLinearMap) x  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem contMDiff_linearMap_trace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    {n : ℕ∞ω} (A : ∀ x : M, V x →L[ℝ] V x)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun x : M => (⟨x, A x⟩ : TotalSpace (F →L[ℝ] F)
        (fun y : M => V y →L[ℝ] V y)))) :
    ContMDiff I 𝓘(ℝ) n
      (fun x : M => LinearMap.trace ℝ (V x) (A x).toLinearMap)  := by sorry

end DifferentialGeometry

