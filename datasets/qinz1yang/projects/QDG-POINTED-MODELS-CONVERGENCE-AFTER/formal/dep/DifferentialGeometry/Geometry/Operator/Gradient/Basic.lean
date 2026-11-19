import dep.DifferentialGeometry.Geometry.Coordinates.Fields.Scalar
import dep.DifferentialGeometry.Geometry.Coordinates.Fields.Vector
import dep.DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import dep.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import dep.DifferentialGeometry.Geometry.Metric.Duality
import dep.DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import dep.DifferentialGeometry.Tensor.Coordinates.PartialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.Coordinates

namespace DifferentialGeometry
namespace Geometry
namespace Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def gradFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap

@[simp] lemma gradFun_def (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradFun (I := I) g f x =
      metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap  := by sorry

lemma inner_gradFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = mfderiv I 𝓘(ℝ, ℝ) f x v  := by sorry

lemma inner_gradFun_right (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x v (gradFun (I := I) g f x) = mfderiv I 𝓘(ℝ, ℝ) f x v  := by sorry

lemma gradFun_eq_zero_of_mfderiv_eq_zero
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) {x : M}
    (hf : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    gradFun (I := I) g f x = (0 : TangentSpace I x)  := by sorry

def chartInvGramMatrix (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x)⁻¹

lemma chartInvGramMatrix_mul_chartGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartInvGramMatrix (I := I) g α x * DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x = 1  := by sorry

lemma chartGramMatrix_mul_chartInvGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x * chartInvGramMatrix (I := I) g α x = 1  := by sorry

lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet  := by sorry

lemma chartInvGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet  := by sorry

noncomputable def chartInvGramMatrixL1Sum
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) : ℝ :=
  ∑ ij : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)),
    |chartInvGramMatrix (I := I) g α x ij.1 ij.2|

lemma chartInvGramMatrix_l1Sum_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    0 ≤ chartInvGramMatrixL1Sum (I := I) (M := M) g α x  := by sorry

lemma chartInvGramMatrix_l1Sum_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (chartInvGramMatrixL1Sum (I := I) (M := M) g α)
      (chartAt H α).source  := by sorry

def gradChartCoeff (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α x i j *
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)

@[simp] lemma gradChartCoeff_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    gradChartCoeff (I := I) g α f i x =
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)  := by sorry

def gradChartLocal (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    gradChartCoeff (I := I) g α f i x •
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x

lemma mfderiv_chartBasisVecFiber_of_mdifferentiableAt
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hxchart : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, ℝ) f x (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x)  := by sorry

lemma inner_gradChartLocal_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner x (gradChartLocal (I := I) g α f x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)
      = DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x)  := by sorry

lemma gradChartLocal_eq_gradFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    gradChartLocal (I := I) g α f x = gradFun (I := I) g f x  := by sorry

theorem chartBasisFamily_repr_gradFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBasisFamily (I := I) α hx).repr (gradFun (I := I) g f x) i =
      gradChartCoeff (I := I) g α f i x  := by sorry

theorem grad_norm_sq_chart_of_mem_interior
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H α).source)
    (hxint : extChartAt I α x ∈ interior (extChartAt I α).target) :
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) =
      ∑ i, ∑ j, chartInvGramMatrix (I := I) g α x i j *
        partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) *
        partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x)  := by sorry

theorem g_inner_gradFun_le_chartInvGramMatrix_l1Sum_mul_sum_sq_partials_of_mem_interior
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H α).source)
    (hxint : extChartAt I α x ∈ interior (extChartAt I α).target) :
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) ≤
      chartInvGramMatrixL1Sum (I := I) (M := M) g α x *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α f)
            (extChartAt I α x)) ^ 2  := by sorry

theorem grad_norm_sq_chart
    (g : SmoothRiemannianMetric I M) [I.Boundaryless]
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H α).source) :
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) =
      ∑ i, ∑ j, chartInvGramMatrix (I := I) g α x i j *
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) *
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x)  := by sorry

theorem g_inner_gradFun_le_chartInvGramMatrix_l1Sum_mul_sum_sq_partials
    (g : SmoothRiemannianMetric I M) [I.Boundaryless]
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H α).source) :
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) ≤
      chartInvGramMatrixL1Sum (I := I) (M := M) g α x *
        ∑ k : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (scalarOnE (I := I) α f)
            (extChartAt I α x)) ^ 2  := by sorry

private lemma gradChartCoeff_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeff (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target)  := by sorry

private lemma gradChartLocal_contMDiffOn_total
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target)  := by sorry

private lemma gradChartLocal_contMDiffOn_total_baseSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      (chartAt H α).source  := by sorry

lemma gradFun_contMDiff_total [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))  := by sorry

def gradG [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => gradFun (I := I) g f x, gradFun_contMDiff_total (I := I) g f.contMDiff⟩

@[simp] lemma grad_g_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    (gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      gradFun (I := I) g f x  := by sorry

theorem tangentSectionAction_eq_inner_grad_g [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) X f x =
      g.inner x (X x)
        ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)  := by sorry

theorem inner_grad_g_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (f h : C^∞⟮I, M; ℝ⟯)
    (x : M) :
    g.inner x ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g h : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((gradG (I := I) g h : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)  := by sorry

lemma gradFun_eq_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ))) :
    gradFun (I := I) g f x = (0 : TangentSpace I x)  := by sorry

lemma support_gradFun_subset
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    Function.support (fun x : M => gradFun (I := I) g f x) ⊆ tsupport f  := by sorry

lemma hasCompactSupport_grad_g [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (hf_cs : HasCompactSupport f) :
    HasCompactSupport ((gradG (I := I) g f :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯))  := by sorry

end Operator
end Geometry
end DifferentialGeometry

end

open Manifold
open scoped ContDiff Manifold NNReal

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Operator

theorem grad_norm_le_of_mvfderiv_bound
    (metric : DifferentialGeometry.SmoothRiemannianMetric I M)
    {u : M → ℝ} {x : M} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ v : TangentSpace I x,
      |mvfderiv (I := I) u x v| ≤ C * Real.sqrt (metric.inner x v v)) :
    Real.sqrt (metric.inner x (gradFun metric u x) (gradFun metric u x)) ≤ C  := by sorry

end

