import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import dep.DifferentialGeometry.Tensor.Coordinates.ModelBasis
import dep.DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
lemma trivializationAt_baseSet_eq_chartAt_source (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet =
      (chartAt H x₀).source  := by sorry

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma extChartAt_source_eq_chartAt_source (x₀ : M) :
    (extChartAt I x₀).source = (chartAt H x₀).source  := by sorry

omit [Module.Finite ℝ E] in
lemma extChartAt_symm_mem_trivializationAt_baseSet (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I) x₀).baseSet  := by sorry

def centeredChartTangentEquiv (x : M) : TangentSpace I x ≃L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)

def centeredChartTangentBasis (x : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (chartModelBasis E).map
    (centeredChartTangentEquiv (I := I) x).symm.toLinearEquiv

omit [Module.Finite ℝ E] in
@[simp] lemma centeredChartTangentEquiv_apply (x : M) (v : TangentSpace I x) :
    centeredChartTangentEquiv (I := I) x v =
      tangentSpaceModelContinuousLinearEquiv (I := I) x v  := by sorry

omit [Module.Finite ℝ E] in
@[simp] lemma centeredChartTangentEquiv_symm_apply (x : M) (v : E) :
    (centeredChartTangentEquiv (I := I) x).symm v = v  := by sorry

@[simp] lemma centeredChartTangentBasis_apply (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    centeredChartTangentBasis (I := I) x i =
      (centeredChartTangentEquiv (I := I) x).symm (chartModelBasis E i)  := by sorry

lemma tangent_model_equiv_centered_chart_basis (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    tangentSpaceModelContinuousLinearEquiv (I := I) x
        (centeredChartTangentBasis (I := I) x i) =
      chartModelBasis E i  := by sorry

lemma tangent_model_equiv_symm_chart_basis (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (chartModelBasis E i) =
      centeredChartTangentBasis (I := I) x i  := by sorry

@[simp] lemma centeredChartTangentBasis_repr (x : M) (v : TangentSpace I x) :
    (centeredChartTangentBasis (I := I) x).repr v =
      (chartModelBasis E).repr (centeredChartTangentEquiv (I := I) x v)  := by sorry

def chartBasisVecFiber (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ x ((chartModelBasis E) i)

theorem localFrame_eq_chartBasisVec
    (alpha : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) alpha).baseSet)
    (i : Fin (Module.finrank Real E)) :
    (trivializationAt E (TangentSpace I) alpha).localFrame
        (chartModelBasis E) i x =
      chartBasisVecFiber (I := I) alpha i x  := by sorry

def chartBasisVec (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    M → TotalSpace E (TangentSpace I : M → Type _) :=
  fun x => TotalSpace.mk' E x (chartBasisVecFiber (I := I) x₀ i x)

@[simp] lemma chartBasisVec_proj (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).proj = x  := by sorry

@[simp] lemma chartBasisVec_snd (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).2 = chartBasisVecFiber (I := I) x₀ i x  := by sorry

lemma trivializationAt_chartBasisVec_snd
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt E (TangentSpace I) x₀
        ⟨x, chartBasisVecFiber (I := I) x₀ i x⟩).2
      = (chartModelBasis E) i  := by sorry

lemma chartBasisVec_contMDiffOn
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) x₀ i)
      (trivializationAt E (TangentSpace I) x₀).baseSet  := by sorry

lemma chartAlphaFrame_section_contMDiffOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I I.tangent ∞
      (fun b : M => TotalSpace.mk' E b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b
          (chartModelBasis E i)))
      (chartAt H α).source  := by sorry

def chartBasisFamily (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (chartModelBasis E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hx).symm)

lemma chartBasisFamily_apply (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) x₀ hx i =
      chartBasisVecFiber (I := I) x₀ i x  := by sorry

lemma chartBasisFamily_linearIndependent (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) x₀ i x)  := by sorry

theorem mfderiv_chartModelBasis_eq_sum
    (f : E → M) {x : E} (hf : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x)
    (y₀ : M) (hy : f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i) =
      ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
            (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap) k i •
        chartBasisVecFiber (I := I) y₀ k (f x)  := by sorry

end DifferentialGeometry.Tensor.Coordinates

