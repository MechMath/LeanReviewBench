import dep.DifferentialGeometry.Integral.Measure.ChartDensity
import dep.DifferentialGeometry.Integral.Measure.Glue
import dep.DifferentialGeometry.Integral.Measure.Invariance
import dep.DifferentialGeometry.Integral.Measure.Properties
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Compactness.LocallyFinite



noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

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




def riemannianMeasureFamily
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) : ℝ → MeasureTheory.Measure M :=
  fun t => riemannianVolumeMeasure (I := I) (M := M) (g_fam t)


lemma riemannianMeasureFamily_def
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) :
    riemannianMeasureFamily (I := I) (M := M) g_fam t =
      riemannianVolumeMeasure (I := I) (M := M) (g_fam t)  := by sorry

structure MetricFamilyRegularAt
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t₀ : ℝ) : Prop where
  
  hasDerivAt_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)) {x : M},
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
          (deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t
  
  continuousOn_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
  
  continuousOn_deriv_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ p.2 i j) p.1)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)


lemma MetricFamilyRegularAt.at_any
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (s : ℝ) :
    MetricFamilyRegularAt (I := I) g_fam s  := by sorry

structure FunctionRegularAt (f : ℝ → M → ℝ) (t₀ : ℝ) : Prop where
  
  hasDerivAt_time :
    ∀ (x : M) (t : ℝ), HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t
  
  continuous_joint : Continuous (fun p : ℝ × M => f p.1 p.2)
  
  continuous_deriv_joint :
    Continuous (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)



section Jacobi

variable {n : Type*} [Fintype n] [DecidableEq n]


lemma hasDerivAt_prod_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (σ : Equiv.Perm n) :
    HasDerivAt (fun t => ∏ i, G t (σ i) i)
      (∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) • G' (σ k) k) t  := by sorry

theorem hasDerivAt_det_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t) :
    HasDerivAt (fun t => (G t).det)
      (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t  := by sorry

theorem perm_sum_eq_trace_adjugate_mul
    (A B : Matrix n n ℝ) :
    (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ k, (∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k)
      = trace (adjugate A * B)  := by sorry

theorem hasDerivAt_det_eq_trace_adjugate_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t) :
    HasDerivAt (fun t => (G t).det)
      (trace (adjugate (G t) * G')) t  := by sorry

lemma adjugate_eq_det_smul_inv
    {A : Matrix n n ℝ} (h : IsUnit A.det) :
    adjugate A = A.det • A⁻¹  := by sorry

theorem hasDerivAt_det_eq_det_mul_trace_inv_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hunit : IsUnit (G t).det) :
    HasDerivAt (fun t => (G t).det)
      ((G t).det * trace ((G t)⁻¹ * G')) t  := by sorry

theorem hasDerivAt_sqrt_det_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hpos : 0 < (G t).det) :
    HasDerivAt (fun s => Real.sqrt (G s).det)
      ((1 / (2 * Real.sqrt (G t).det)) *
        ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t  := by sorry

theorem hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hpos : 0 < (G t).det) :
    HasDerivAt (fun s => Real.sqrt (G s).det)
      ((1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det) t  := by sorry

end Jacobi



section ChartDensityFamily

variable {g_fam : ℝ → SmoothRiemannianMetric I M}


def chartGramMatrixFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun t => chartGramMatrix (I := I) (g_fam t) x₀ x

@[simp] lemma chartGramMatrixFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartGramMatrixFamily (I := I) g_fam x₀ x t =
      chartGramMatrix (I := I) (g_fam t) x₀ x  := by sorry

def chartDensityFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → ℝ :=
  fun t => chartDensity (I := I) (g_fam t) x₀ x

@[simp] lemma chartDensityFamily_apply
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      chartDensity (I := I) (g_fam t) x₀ x  := by sorry

lemma chartDensityFamily_eq_sqrt_det
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) (t : ℝ) :
    chartDensityFamily (I := I) g_fam x₀ x t =
      Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det  := by sorry

theorem hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ : M) (t : ℝ) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (Gprime : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hEntries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam x₀ x s i j)
        (Gprime i j) t) :
    HasDerivAt
      (fun s => chartDensityFamily (I := I) g_fam x₀ x s)
      ((1 / 2) *
        trace ((chartGramMatrixFamily (I := I) g_fam x₀ x t)⁻¹ * Gprime) *
        Real.sqrt (chartGramMatrixFamily (I := I) g_fam x₀ x t).det) t  := by sorry

end ChartDensityFamily



variable (I) in

def traceTimeDerivMetric
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) : ℝ :=
  Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
    (Matrix.of fun i j =>
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t))


lemma traceTimeDerivMetric_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    traceTimeDerivMetric (I := I) g_fam t x =
      Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
        (Matrix.of fun i j =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t))  := by sorry

theorem integral_chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (h : M → ℝ) (hh_meas : Measurable h) :
    ∫ x, h x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ y in (extChartAt I x₀).target,
          chartDensity g x₀ ((extChartAt I x₀).symm y) *
            h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E))  := by sorry

lemma chartAtlasPOU_finite_support
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] :
    {α : M | (Function.support ((chartAtlasPOU I M) α)).Nonempty}.Finite  := by sorry

noncomputable def chartAtlasPOU_finset
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] : Finset M :=
  (chartAtlasPOU_finite_support (I := I) (M := M)).toFinset

lemma chartAtlasPOU_finset_mem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] {α : M} :
    α ∈ chartAtlasPOU_finset (I := I) (M := M) ↔
      (Function.support ((chartAtlasPOU I M) α)).Nonempty  := by sorry

lemma chartAtlasPOU_weight_zero_of_notMem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M)) (x : M) :
    (chartAtlasPOU I M) α x = 0  := by sorry

lemma chartAtlasPOU_withDensity_zero_of_notMem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M)) :
    (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) = 0  := by sorry

theorem hasDerivAt_setIntegral_model
    (target : Set E) (_htarget_meas : MeasurableSet target)
    {F : ℝ → E → ℝ} (F' : ℝ → E → ℝ) {b : E → ℝ}
    (t₀ : ℝ) {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (hF_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (F t) ((modelHaar (E := E)).restrict target))
    (hF_int : Integrable (F t₀) ((modelHaar (E := E)).restrict target))
    (hF'_meas : AEStronglyMeasurable (F' t₀)
      ((modelHaar (E := E)).restrict target))
    (h_bound : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ t ∈ s, ‖F' t y‖ ≤ b y)
    (h_bound_int : Integrable b ((modelHaar (E := E)).restrict target))
    (h_diff : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ t ∈ s, HasDerivAt (fun r => F r y) (F' t y) t) :
    Integrable (F' t₀) ((modelHaar (E := E)).restrict target) ∧
      HasDerivAt (fun t => ∫ y in target, F t y ∂(modelHaar (E := E)))
        (∫ y in target, F' t₀ y ∂(modelHaar (E := E))) t₀  := by sorry

lemma hasDerivAt_chartGramMatrix_entry
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i j : Fin (Module.finrank ℝ E)) (t : ℝ) :
    HasDerivAt (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
      (deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t  := by sorry

section ChartInvarianceOfTraceTimeDeriv


lemma deriv_chartGramMatrix_pullback
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t)
      = (transitionMatrix (I := I) x₀ x₁ x)ᵀ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) *
          transitionMatrix (I := I) x₀ x₁ x  := by sorry

lemma transitionMatrix_mul_reverse
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    transitionMatrix (I := I) x₀ x₁ x * transitionMatrix (I := I) x₁ x₀ x = 1  := by sorry

lemma transitionMatrix_isUnit
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    IsUnit (transitionMatrix (I := I) x₀ x₁ x)  := by sorry

lemma trace_chartGramMatrix_inv_deriv_chart_independent
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x₀ x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t))
    = Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x₁ x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t))  := by sorry

end ChartInvarianceOfTraceTimeDeriv


lemma traceTimeDerivMetric_eq_trace_chartGramMatrix
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    traceTimeDerivMetric (I := I) g_fam t x
    = Matrix.trace ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t))  := by sorry

theorem riemannianVolumeMeasure_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x))  := by sorry

theorem integral_riemannianVolumeMeasure_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (h : M → ℝ)
    (hh_cont : Continuous h) :
    ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∫ x, h x
            ∂((chartLocalMeasure (I := I) g α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y)))  := by sorry

theorem volume_variation_formula_from_chart_derivs
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (Iα : M → ℝ)
    (Iglobal : ℝ)
    (hα_deriv : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (Iα α) t)
    (hα_sum_val : ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Iα α = Iglobal) :
    HasDerivAt
      (fun s : ℝ => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
      Iglobal t  := by sorry

theorem integral_riemannianMeasureFamily_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (hf_cont : Continuous (f t)) :
    ∫ x, f t x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t)
      = ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∫ x, f t x
            ∂((chartLocalMeasure (I := I) (g_fam t) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y)))  := by sorry

theorem volume_variation_formula
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (Iα : M → ℝ) (Iglobal : ℝ)
    (hf_cont : ∀ᶠ s in 𝓝 t, Continuous (f s))
    (hα_deriv : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (Iα α) t)
    (hα_sum_val : ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Iα α = Iglobal) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      Iglobal t  := by sorry

section CleanVolumeVariation

variable {g_fam : ℝ → SmoothRiemannianMetric I M}


lemma per_chart_integrand_hasDerivAt
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (f : ℝ → M → ℝ) (ρ : M → ℝ)
    (hf : HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t) :
    HasDerivAt
      (fun s : ℝ => f s x * ρ x *
        chartDensity (I := I) (g_fam s) α x)
      ((deriv (fun s : ℝ => f s x) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρ x *
        chartDensity (I := I) (g_fam t) α x) t  := by sorry

theorem chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (h : M → ℝ) (hh_cont : Continuous h) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)
      = ∫ x, h x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t)  := by sorry

theorem volume_variation_formula_clean_of_chart_derivs
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (hf_cont : ∀ᶠ s in 𝓝 t, Continuous (f s))
    (hh_cont : Continuous
      (fun x : M => deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x))
    (hα_deriv_explicit : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (∫ x, (deriv (fun s : ℝ => f s x) t +
                (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
              (chartAtlasPOU I M) α x
            ∂(chartLocalMeasure (I := I) (g_fam t) α)) t) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t +
              (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t))
      t  := by sorry

section TraceTimeDerivMetricContinuous


lemma continuousOn_traceTimeDerivMetric_on_base
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) :
    ContinuousOn
      (fun p : ℝ × M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)  := by sorry

lemma traceTimeDerivMetric_continuous
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) :
    Continuous (fun x : M => traceTimeDerivMetric (I := I) g_fam t x)  := by sorry

lemma continuousOn_traceTimeDerivMetric_of_base
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M) :
    ContinuousOn
      (fun p : ℝ × M => traceTimeDerivMetric (I := I) g_fam p.1 p.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)  := by sorry

lemma continuousOn_chartDensity_family
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M) :
    ContinuousOn
      (fun p : ℝ × M => chartDensity (I := I) (g_fam p.1) α p.2)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)  := by sorry

lemma continuousOn_chartTrace_form_of_base_pullback
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M)
    {S : Set (ℝ × E)} (sym : E → M)
    (hsym_cont : ContinuousOn (fun p : ℝ × E => (p.1, sym p.2)) S)
    (hsym_maps : Set.MapsTo (fun p : ℝ × E => ((p.1, sym p.2) : ℝ × M)) S
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn
      (fun p : ℝ × E => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α (sym p.2))⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α (sym p.2) i j) p.1)))
      S  := by sorry

end TraceTimeDerivMetricContinuous



section PerChartHasDerivAt

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

private lemma chartDensity_nonneg_of_base
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    0 ≤ chartDensity (I := I) g α x  := by sorry

set_option maxHeartbeats 16000000 in




lemma per_chart_hasDerivAt
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M} {f : ℝ → M → ℝ} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (hf : FunctionRegularAt f t)
    (α : M) (_hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
      (∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
            (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)) t  := by sorry

end PerChartHasDerivAt



section CleanTheorem

variable {g_fam : ℝ → SmoothRiemannianMetric I M}


theorem volume_variation_formula_clean
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    {f : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t₀
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀  := by sorry

end CleanTheorem

end CleanVolumeVariation

end Measure
end Integral
end DifferentialGeometry
