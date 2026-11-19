import dep.DifferentialGeometry.Integral.L2.SmoothSections.Defs
import dep.DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Analysis.Normed.Operator.Bilinear



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]



private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




noncomputable def dualCovariantCMM (r : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
    (fun k : Fin r =>
      LinearMap.toContinuousLinearMap ((chartModelBasis E).coord (Idx k)))

@[simp] lemma dualCovariantCMM_apply (r : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E)) (v : Fin r → E) :
    dualCovariantCMM (E := E) r Idx v =
      ∏ k : Fin r, ((chartModelBasis E).coord (Idx k)) (v k)  := by sorry

lemma dualCovariantCMM_apply_basis_tuple (r : ℕ)
    (Idx Jdx : Fin r → Fin (Module.finrank ℝ E)) :
    dualCovariantCMM (E := E) r Idx
        (fun k : Fin r => chartModelBasis E (Jdx k)) =
      if Idx = Jdx then (1 : ℝ) else 0  := by sorry

noncomputable def tensorChartComponentProjection (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    TensorRSModel r s ℝ E →L[ℝ] ℝ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ
      (fun k : Fin s => chartModelBasis E (Jdx k))).comp
    (ContinuousLinearMap.apply ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
      (dualCovariantCMM (E := E) r Idx))

@[simp] lemma tensorChartComponentProjection_apply (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (T : TensorRSModel r s ℝ E) :
    tensorChartComponentProjection (E := E) r s Idx Jdx T =
      T (dualCovariantCMM (E := E) r Idx)
        (fun k : Fin s => chartModelBasis E (Jdx k))  := by sorry

noncomputable def tensorChartBasisElement (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    TensorRSModel r s ℝ E :=
  ContinuousLinearMap.smulRight
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => E) ℝ
      (fun k : Fin r => chartModelBasis E (Idx k)))
    (dualCovariantCMM (E := E) s Jdx)

@[simp] lemma tensorChartBasisElement_apply (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (w : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) :
    tensorChartBasisElement (E := E) r s Idx Jdx w =
      w (fun k : Fin r => chartModelBasis E (Idx k)) •
        dualCovariantCMM (E := E) s Jdx  := by sorry

lemma tensorChartComponentProjection_basisElement (r s : ℕ)
    (Idx₁ Idx₂ : Fin r → Fin (Module.finrank ℝ E))
    (Jdx₁ Jdx₂ : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx₁ Jdx₁
        (tensorChartBasisElement (E := E) r s Idx₂ Jdx₂) =
      (if Idx₁ = Idx₂ then (1 : ℝ) else 0) *
        (if Jdx₂ = Jdx₁ then (1 : ℝ) else 0)  := by sorry

private lemma cmm_eq_sum_basis_coeffs (s : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    f = ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          f (fun k : Fin s => chartModelBasis E (Jdx k)) •
            dualCovariantCMM (E := E) s Jdx  := by sorry

theorem tensorRSModel_eq_sum_basis (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    T = ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx T •
              tensorChartBasisElement (E := E) r s Idx Jdx  := by sorry

noncomputable def tensorChartBasisNormConstant (r s : ℕ) : ℝ :=
  ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
    ‖tensorChartBasisElement (E := E) r s p.1 p.2‖

lemma tensorChartBasisNormConstant_nonneg (r s : ℕ) :
    0 ≤ tensorChartBasisNormConstant (E := E) r s  := by sorry

lemma tensorChartBasisElement_norm_le (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ ≤
      tensorChartBasisNormConstant (E := E) r s  := by sorry

noncomputable def tensorTrivProj
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (x : M) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x
      (S.toSection x)


noncomputable def tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (x : M) : ℝ :=
  tensorChartComponentProjection (E := E) r s Idx Jdx
    (tensorTrivProj (I := I) (M := M) g r s S α x)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
end
