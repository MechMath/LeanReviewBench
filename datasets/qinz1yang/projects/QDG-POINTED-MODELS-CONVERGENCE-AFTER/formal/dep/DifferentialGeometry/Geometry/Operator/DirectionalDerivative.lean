import dep.DifferentialGeometry.Tensor.Coordinates.PartialDerivative
import dep.DifferentialGeometry.Geometry.Coordinates.Fields.Scalar
import dep.DifferentialGeometry.Geometry.Coordinates.Fields.Vector
import dep.DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

export DifferentialGeometry.Tensor.Coordinates
  (chartCoeff chartCoeff_contMDiffOn chartCoeff_def chartCoeff_recompose chartCoeffOnE
    chartCoeffOnE_contDiffOn extChartAt_source_eq_chartAt_source scalarOnE scalarOnE_contDiffOn
    scalarOnE_contDiffWithinAt scalarOnE_def scalarOnE_extChartAt
    trivializationAt_baseSet_eq_chartAt_source)

def tangentSectionAction
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) : M → ℝ :=
  fun x => mfderiv I 𝓘(ℝ) f x (X x)

omit [Module.Finite ℝ E] in
lemma tsupport_tangentSectionAction_subset_right
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) :
    tsupport (tangentSectionAction (I := I) X f) ⊆ tsupport f  := by sorry

omit [Module.Finite ℝ E] in
@[simp] lemma tangentSectionAction_def
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) (x : M) :
    tangentSectionAction (I := I) X f x = mfderiv I 𝓘(ℝ) f x (X x)  := by sorry

omit [Module.Finite ℝ E] in
theorem tangent_mul
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    tangentSectionAction (I := I) X (fun y => f y * h y) x =
      f x * tangentSectionAction (I := I) X h x +
        h x * tangentSectionAction (I := I) X f x  := by sorry

def chartPullZero (α : M) (f : M → ℝ) : E → ℝ :=
  (extChartAt I α).target.indicator (scalarOnE (I := I) α f)
omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma chartPullZero_mem (α : M) (f : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    chartPullZero (I := I) α f y = scalarOnE (I := I) α f y  := by sorry

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma chartPullZero_nmem (α : M) (f : M → ℝ) {y : E}
    (hy : y ∉ (extChartAt I α).target) :
    chartPullZero (I := I) α f y = 0  := by sorry

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem tsupport_chartPullZero_subset_image
    (α : M) {f : M → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt H α).source) :
    tsupport (chartPullZero (I := I) α f) ⊆ (extChartAt I α) '' tsupport f  := by sorry

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem hasCompactSupport_chartPullZero
    (α : M) {f : M → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPullZero (I := I) α f)  := by sorry

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem tsupport_chartPullZero_subset_target
    (α : M) {f : M → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt H α).source) :
    tsupport (chartPullZero (I := I) α f) ⊆ (extChartAt I α).target  := by sorry

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem chartPullZero_contDiffOn
    {k : WithTop ℕ∞} [IsManifold I k M]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) k f) :
    ContDiffOn ℝ k (chartPullZero (I := I) α f) (extChartAt I α).target  := by sorry

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem chartPullZero_contDiffOn_range
    {k : WithTop ℕ∞} [IsManifold I k M]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) k f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt H α).source) :
    ContDiffOn ℝ k (chartPullZero (I := I) α f) (Set.range I)  := by sorry

lemma mfderiv_chart_diff (α : M)
    {f : M → ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hf : DifferentiableAt ℝ (scalarOnE (I := I) α f) (extChartAt I α x))
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x)  := by sorry

lemma mfderiv_chartBasisVecFiber (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
      = DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x)  := by sorry

theorem tangentSectionAction_chartLocal
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x)  := by sorry

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma extChartAt_target_subset_interior_of_boundaryless [I.Boundaryless] (α : M) :
    (extChartAt I α).target ⊆ interior (extChartAt I α).target  := by sorry

theorem tangent_chart_diff [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hf : DifferentiableAt ℝ (chartPullZero (I := I) α f)
      (extChartAt I α x)) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          lineDeriv ℝ (chartPullZero (I := I) α f) (extChartAt I α x)
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)  := by sorry

theorem tangentSectionAction_chartLocal_of_boundaryless [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x)  := by sorry

private lemma partialDeriv_scalarOnE_contDiffOn_interior
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target)  := by sorry

private lemma partialDeriv_scalarOnE_comp_extChartAt_contMDiffOn
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target)  := by sorry

theorem tangentSectionAction_contMDiffOn
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target)  := by sorry

theorem tangentSectionAction_contMDiffOn_baseSet [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      (chartAt H α).source  := by sorry

omit [Module.Finite ℝ E] in
theorem tangentSectionAction_contMDiff
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)  := by sorry

omit [Module.Finite ℝ E] in
theorem mfderiv_eq_fderivWithin_scalarOnE
    (α : M) {f : M → ℝ} {x : M}
    (hx : x ∈ (chartAt H α).source) (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ) f x v =
      fderivWithin ℝ (scalarOnE (I := I) α f) (extChartAt I α).target (extChartAt I α x)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)  := by sorry

omit [Module.Finite ℝ E] in
theorem tangentSectionAction_eq_fderivWithin_scalarOnE
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    tangentSectionAction X f x =
      fderivWithin ℝ (scalarOnE (I := I) α f) (extChartAt I α).target (extChartAt I α x)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (X x))  := by sorry

end DivergenceTheorem
end Integral
end DifferentialGeometry

