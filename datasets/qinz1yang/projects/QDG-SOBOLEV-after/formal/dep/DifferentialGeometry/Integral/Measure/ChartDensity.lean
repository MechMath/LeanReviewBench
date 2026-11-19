import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

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


abbrev SmoothRiemannianMetric (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)




@[irreducible] def chartModelBasis (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map
    (toEuclidean (E := E)).symm.toLinearEquiv

@[simp] lemma chartModelBasis_apply (i : Fin (Module.finrank ℝ E)) :
    chartModelBasis E i =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ))  := by sorry

def chartBasisVecFiber (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symm x ((chartModelBasis E) i)


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

def chartGramMatrix (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) x₀ i x)
      (chartBasisVecFiber (I := I) x₀ j x)

@[simp] lemma chartGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g x₀ x i j =
      g.inner x
        (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ j x)  := by sorry

lemma chartGramMatrix_isHermitian
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    (chartGramMatrix g x₀ x).IsHermitian  := by sorry

lemma chartGramMatrix_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (chartGramMatrix g x₀ x) *ᵥ c =
      g.inner x
        (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
        (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x)  := by sorry

lemma chartGramMatrix_posDef
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (chartGramMatrix g x₀ x).PosDef  := by sorry

lemma chartGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < (chartGramMatrix g x₀ x).det  := by sorry

def chartDensity (g : SmoothRiemannianMetric I M) (x₀ : M) : M → ℝ :=
  fun x => Real.sqrt (chartGramMatrix g x₀ x).det


lemma chartDensity_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < chartDensity g x₀ x  := by sorry

lemma chartGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix g x₀ x i j)
      (trivializationAt E (TangentSpace I) x₀).baseSet  := by sorry

private lemma chartGramMatrix_pair_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix g x₀ x ij.1 ij.2)
      (trivializationAt E (TangentSpace I) x₀).baseSet  := by sorry

lemma chartGramMatrix_det_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => (chartGramMatrix g x₀ x).det)
      (trivializationAt E (TangentSpace I) x₀).baseSet  := by sorry

lemma chartDensity_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet  := by sorry

noncomputable def modelHaar : MeasureTheory.Measure E := (chartModelBasis E).addHaar


instance modelHaar_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure (modelHaar (E := E)) := by
  unfold modelHaar
  infer_instance


theorem map_toEuclidean_modelHaar_eq_volume :
    MeasureTheory.Measure.map (toEuclidean (E := E)) (modelHaar (E := E)) =
      (MeasureTheory.volume :
        MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))  := by sorry

def chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.map (extChartAt I x₀).symm
    (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
      (fun y : E =>
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y))))


lemma chartLocalMeasure_def
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    chartLocalMeasure (I := I) g x₀ =
      MeasureTheory.Measure.map (extChartAt I x₀).symm
        (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
          (fun y : E =>
            ENNReal.ofReal
              (chartDensity g x₀ ((extChartAt I x₀).symm y))))  := by sorry

end Measure
end Integral
end DifferentialGeometry
