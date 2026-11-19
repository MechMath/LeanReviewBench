import dep.DifferentialGeometry.Integral.Measure.ChartDensity
import dep.DifferentialGeometry.Integral.Measure.Glue
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal Matrix

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




lemma extChartAt_symm_preimage_inter_target_eq_empty
    (x₀ : M) {A : Set M} (hA : Disjoint A (chartAt H x₀).source) :
    (extChartAt I x₀).symm ⁻¹' A ∩ (extChartAt I x₀).target = ∅  := by sorry

lemma measurableSet_extChartAt_target (x₀ : M) :
    MeasurableSet (extChartAt I x₀).target  := by sorry

theorem chartLocalMeasure_apply_of_disjoint_source
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {A : Set M} (hAmeas : MeasurableSet A)
    (hA : Disjoint A (chartAt H x₀).source) :
    chartLocalMeasure (I := I) g x₀ A = 0  := by sorry

variable (E) in

theorem euclideanChangeOfVariablesMap
    {s : Set E}
    (hs : NullMeasurableSet s (modelHaar (E := E)))
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map f
        (((modelHaar (E := E)).restrict s).withDensity
          (fun x => ENNReal.ofReal |(f' x).det|)) =
      (modelHaar (E := E)).restrict (f '' s)  := by sorry

lemma tangentCoordChange_eq_fderivWithin
    (x₀ x₁ : M) {x : M}
    (_h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    tangentCoordChange I x₀ x₁ x =
      fderivWithin ℝ (extChartAt I x₁ ∘ (extChartAt I x₀).symm) (range I)
        (extChartAt I x₀ x)  := by sorry

lemma tangentCoordChange_hasFDerivWithinAt
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    HasFDerivWithinAt (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
      (tangentCoordChange I x₀ x₁ x) (range I) (extChartAt I x₀ x)  := by sorry

lemma chartModelBasis_repr_sum
    (L : E →L[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    L ((chartModelBasis E) i) =
      ∑ k, ((chartModelBasis E).repr (L ((chartModelBasis E) i)) k)
            • (chartModelBasis E) k  := by sorry

def transitionMatrix (x₀ x₁ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i =>
    (chartModelBasis E).repr
      ((tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) i)) k

@[simp] lemma transitionMatrix_apply (x₀ x₁ : M) (x : M)
    (k i : Fin (Module.finrank ℝ E)) :
    transitionMatrix (I := I) x₀ x₁ x k i =
      (chartModelBasis E).repr
        ((tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) i)) k  := by sorry

lemma tangentCoordChange_chartModelBasis_eq_sum
    (x₀ x₁ : M) (x : M) (i : Fin (Module.finrank ℝ E)) :
    (tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) i) =
      ∑ k, transitionMatrix (I := I) x₀ x₁ x k i • (chartModelBasis E) k  := by sorry

lemma chartBasisVecFiber_pullback
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x₁ i x =
      ∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
        chartBasisVecFiber (I := I) x₀ k x  := by sorry

lemma chartGramMatrix_pullback_eq_sum
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g x₁ x i j =
      ∑ k, ∑ l,
        (transitionMatrix (I := I) x₀ x₁ x k i) *
        (transitionMatrix (I := I) x₀ x₁ x l j) *
        chartGramMatrix g x₀ x k l  := by sorry

lemma chartGramMatrix_pullback_eq_mul
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    chartGramMatrix g x₁ x =
      (transitionMatrix (I := I) x₀ x₁ x)ᵀ *
        chartGramMatrix g x₀ x *
        transitionMatrix (I := I) x₀ x₁ x  := by sorry

lemma transitionMatrix_det (x₀ x₁ : M) (x : M) :
    (transitionMatrix (I := I) x₀ x₁ x).det =
      (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det  := by sorry

lemma chartGramMatrix_det_pullback
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    (chartGramMatrix g x₁ x).det =
      ((tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det) ^ 2 *
        (chartGramMatrix g x₀ x).det  := by sorry

theorem chartDensity_pullback_eq_abs_det_jacobian
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    chartDensity g x₁ x =
      |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| *
        chartDensity g x₀ x  := by sorry

lemma trivializationAt_baseSet_eq_chartAt_source (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet = (chartAt H x₀).source  := by sorry

lemma isOpen_chartAt_source_inter (x₀ x₁ : M) :
    IsOpen ((chartAt H x₀).source ∩ (chartAt H x₁).source)  := by sorry

lemma measurableSet_chartAt_source_inter (x₀ x₁ : M) :
    MeasurableSet ((chartAt H x₀).source ∩ (chartAt H x₁).source)  := by sorry

lemma extChartAt_source_eq_chartAt_source (x₀ : M) :
    (extChartAt I x₀).source = (chartAt H x₀).source  := by sorry

lemma chartDensity_continuousOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContinuousOn (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet  := by sorry

variable (I M) in

def riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) : MeasureTheory.Measure M :=
  riemannianMeasure (I := I) g (chartAtlasPOU I M)


lemma riemannianVolumeMeasure_def
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      riemannianMeasure (I := I) g (chartAtlasPOU I M)  := by sorry

lemma aemeasurable_extChartAt_symm_restrict_target
    (x₀ : M) :
    AEMeasurable ((extChartAt I x₀).symm)
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target)  := by sorry

lemma aemeasurable_chartDensity_symm_pullback
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    AEMeasurable
      (fun y : E =>
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)))
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target)  := by sorry

theorem chartLocalMeasure_lintegral
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀).target,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E))  := by sorry

lemma tangentCoordChange_comp_self_overlap
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) (v : E) :
    tangentCoordChange I x₁ x₀ x (tangentCoordChange I x₀ x₁ x v) = v  := by sorry

lemma tangentCoordChange_det_mul_inv_det_eq_one
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    (tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det *
      (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det = 1  := by sorry

lemma abs_det_tangentCoordChange_mul_abs_det_inv
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
      |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| = 1  := by sorry

lemma ennreal_abs_det_tangentCoordChange_mul_abs_det_inv
    (x₀ x₁ : M) {x : M}
    (h : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source) :
    ENNReal.ofReal |(tangentCoordChange I x₀ x₁ x : E →L[ℝ] E).det| *
      ENNReal.ofReal
        |(tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det| = 1  := by sorry

theorem chartLocalMeasure_setLintegral_indicator
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {U : Set M} (hUmeas : MeasurableSet U)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in U, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀).target,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          U.indicator F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E))  := by sorry

lemma extChartAt_image_isOpen_of_open_subset_source_of_boundaryless
    [I.Boundaryless] (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source) :
    IsOpen ((extChartAt I x₀) '' U)  := by sorry

lemma extChartAt_image_measurableSet_of_open_subset_source (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source) :
    MeasurableSet ((extChartAt I x₀) '' U)  := by sorry

lemma extChartAt_image_measurableSet_of_overlap (x₀ x₁ : M) :
    MeasurableSet ((extChartAt I x₀) ''
      ((chartAt H x₀).source ∩ (chartAt H x₁).source))  := by sorry

lemma extChartAt_transition_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H x₀).source) (_hUsub1 : U ⊆ (chartAt H x₁).source) :
    (extChartAt I x₁ ∘ (extChartAt I x₀).symm) '' ((extChartAt I x₀) '' U) =
      (extChartAt I x₁) '' U  := by sorry

lemma extChartAt_transition_injOn_overlap_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H x₀).source) (hUsub1 : U ⊆ (chartAt H x₁).source) :
    Set.InjOn (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀) '' U)  := by sorry

lemma extChartAt_transition_hasFDerivWithinAt_on_overlap_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H x₀).source) (hUsub1 : U ⊆ (chartAt H x₁).source) :
    ∀ y ∈ (extChartAt I x₀) '' U,
      HasFDerivWithinAt (extChartAt I x₁ ∘ (extChartAt I x₀).symm)
        (tangentCoordChange I x₀ x₁ ((extChartAt I x₀).symm y))
        ((extChartAt I x₀) '' U) y  := by sorry

lemma setLIntegral_target_eq_setLIntegral_image
    (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source)
    (h : E → ℝ≥0∞) :
    ∫⁻ y in (extChartAt I x₀).target,
        (U.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y)) * h y
            ∂(modelHaar (E := E)) =
      ∫⁻ y in (extChartAt I x₀) '' U, h y ∂(modelHaar (E := E))  := by sorry

lemma chartLocalMeasure_lintegral_U_eq_setLIntegral_image
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H x₀).source)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hUmeas : MeasurableSet U) :
    ∫⁻ x in U, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀) '' U,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E))  := by sorry

theorem chartLocalMeasure_lintegral_U_eq_of_overlap
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in (chartAt H x₀).source ∩ (chartAt H x₁).source, F x
        ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ x in (chartAt H x₀).source ∩ (chartAt H x₁).source, F x
        ∂(chartLocalMeasure (I := I) g x₁)  := by sorry

theorem chartLocalMeasure_restrict_overlap_eq
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) :
    (chartLocalMeasure (I := I) g x₀).restrict
        ((chartAt H x₀).source ∩ (chartAt H x₁).source) =
      (chartLocalMeasure (I := I) g x₁).restrict
        ((chartAt H x₀).source ∩ (chartAt H x₁).source)  := by sorry

lemma chartLocalMeasure_lintegral_eq_of_support_in_overlap
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M)
    {f : M → ℝ≥0∞} (hf : Measurable f)
    (hsupp : ∀ x, x ∉ (chartAt H x₀).source ∩ (chartAt H x₁).source → f x = 0) :
    ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ x, f x ∂(chartLocalMeasure (I := I) g x₁)  := by sorry

lemma pou_product_support_subset_overlap
    (ρ ρ' : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (hρ' : ρ'.IsSubordinate (fun α : M => (chartAt H α).source))
    (α β : M) (f : M → ℝ≥0∞) :
    ∀ x, x ∉ (chartAt H α).source ∩ (chartAt H β).source →
      ENNReal.ofReal (ρ α x) * ENNReal.ofReal (ρ' β x) * f x = 0  := by sorry

lemma countable_nonempty_support_of_pou
    [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M univ) :
    Set.Countable {α : M | (Function.support (ρ α)).Nonempty}  := by sorry

lemma tsum_subtype_eq_of_support_subset {s : Set M} {f : M → ℝ≥0∞}
    (h : Function.support f ⊆ s) :
    ∑' x : M, f x = ∑' x : s, f x.val  := by sorry

lemma tsum_ofReal_pou_eq_one
    (ρ' : SmoothPartitionOfUnity M I M univ) (x : M) :
    ∑' β : M, ENNReal.ofReal (ρ' β x) = 1  := by sorry

lemma lintegral_ofReal_pou_zero_of_support_empty
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M)
    (h : Function.support (ρ α) = ∅)
    (μ : MeasureTheory.Measure M) (F : M → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal (ρ α x) * F x ∂μ = 0  := by sorry

lemma tsum_integral_pou_eq_subtype
    [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M univ)
    (cLM : M → MeasureTheory.Measure M) (F : M → ℝ≥0∞) :
    (∑' α : M, ∫⁻ x, ENNReal.ofReal (ρ α x) * F x ∂(cLM α)) =
      ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        ∫⁻ x, ENNReal.ofReal (ρ α.val x) * F x ∂(cLM α.val)  := by sorry

lemma ofReal_pou_mul_expand_on_subtype
    [T2Space M] [SigmaCompactSpace M]
    (ρ ρ' : SmoothPartitionOfUnity M I M univ) (α : M)
    (F : M → ℝ≥0∞) (x : M) :
    ENNReal.ofReal (ρ α x) * F x =
      ∑' β : {β : M | (Function.support (ρ' β)).Nonempty},
        ENNReal.ofReal (ρ α x) * ENNReal.ofReal (ρ' β.val x) * F x  := by sorry

theorem riemannianMeasure_eq_of_pou_independent
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ ρ' : SmoothPartitionOfUnity M I M univ)
    (hρ  : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (hρ' : ρ'.IsSubordinate (fun α : M => (chartAt H α).source)) :
    riemannianMeasure (I := I) g ρ = riemannianMeasure (I := I) g ρ'  := by sorry

theorem riemannianMeasure_independent_of_atlas
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ ρ' : SmoothPartitionOfUnity M I M univ)
    (hρ  : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (hρ' : ρ'.IsSubordinate (fun α : M => (chartAt H α).source)) :
    riemannianMeasure (I := I) g ρ = riemannianMeasure (I := I) g ρ'  := by sorry

theorem riemannianMeasure_eq_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    riemannianMeasure (I := I) g ρ = riemannianVolumeMeasure (I := I) (M := M) g  := by sorry

end Measure
end Integral
end DifferentialGeometry
