import dep.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import dep.DifferentialGeometry.Geometry.Coordinates.Connection.Christoffel
import dep.DifferentialGeometry.Geometry.Coordinates.Frame.Coordinate
import dep.DifferentialGeometry.Geometry.Curvature.Riemann.RawFields
import dep.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import dep.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Mixed
import dep.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import Mathlib.Geometry.Manifold.VectorBundle.Hom
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

noncomputable def metricFlatContinuousEquiv
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E ≃L[Real] (E →L[Real] Real) :=
  let e := (trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt Real x₀
    (FiberBundle.mem_baseSet_trivializationAt' x₀)
  ((e.symm.toLinearEquiv.trans (metricFlatEquiv (I := I) g x₀)).trans
      e.symm.toLinearEquiv.dualMap |>.trans
    (LinearMap.toContinuousLinearMap :
      (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real))).toContinuousLinearEquiv

theorem metricFlatContinuousEquiv_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : E) :
    ((metricFlatContinuousEquiv (I := I) g x₀) v) w =
      g.inner x₀
        ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ v)
        ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w)  := by sorry

noncomputable def metricFlatModelInChart
    (g : SmoothRiemannianMetric I M) (x₀ : M) (y : E) :
    E →L[Real] E →L[Real] Real :=
  (trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
      ⟨(extChartAt I x₀).symm y, g.inner ((extChartAt I x₀).symm y)⟩).2

theorem metricFlatModelInChart_center_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀) =
      (metricFlatContinuousEquiv (I := I) g x₀ :
        E →L[Real] (E →L[Real] Real))  := by sorry

omit [FiniteDimensional ℝ E] in
theorem flatChart_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (v w : E) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v w =
      g.inner x
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w)  := by sorry

theorem flatChart_inv
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)).IsInvertible  := by sorry

theorem coordBasis_model
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    coordinateFrameAtBasis (I := I) x₀ hx i =
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x
        ((Module.finBasis Real E) i)  := by sorry

theorem metricFlatModelInChart_center_isInvertible
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)).IsInvertible  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) (extChartAt I x₀ x₀)  := by sorry

theorem inverseMetricFlatModelInChart_contDiffWithinAt
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ y))
      (Set.range I) (extChartAt I x₀ x₀)  := by sorry

noncomputable def inverseMetricFlatModelInChartComponent
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  (Module.finBasis Real E).coord k
    ((ContinuousLinearMap.inverse
        (metricFlatModelInChart (I := I) g x₀ y))
      (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))


theorem inverseMetricFlatModelInChart_component_contDiffWithinAt
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (inverseMetricFlatModelInChartComponent (I := I) g x₀ k l)
      (Set.range I) (extChartAt I x₀ x₀)  := by sorry

theorem gInvComp_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
          (extChartAt I x₀ y)) x₀  := by sorry

theorem gInvComp_mdiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
          (extChartAt I x₀ y)) x₀  := by sorry

theorem inverseMetricFlatModelInChart_component_center_eq_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricFlatModelInChartComponent (I := I) g x₀ i j
        (extChartAt I x₀ x₀) =
      inverseMetricFlatModelInChartComponent (I := I) g x₀ j i
        (extChartAt I x₀ x₀)  := by sorry

theorem gInvChart_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricFlatModelInChartComponent (I := I) g x₀ i j
        (extChartAt I x₀ x) =
      inverseMetricFlatModelInChartComponent (I := I) g x₀ j i
        (extChartAt I x₀ x)  := by sorry

theorem gInvBasisAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    MetricInverseInBasis (I := I) g x (coordinateFrameAtBasis (I := I) x₀ hx)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
          (extChartAt I x₀ x))  := by sorry

theorem inverseMetricFlatModelInChart_metricInverseInBasis_center
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    MetricInverseInBasis (I := I) g x₀ (coordinateFrameAtToBasis (I := I) x₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
          (extChartAt I x₀ x₀))  := by sorry

def metricCompForMetricInFrame
    (g : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j : Idx) : Real :=
  g.inner x (frame i x) (frame j x)

theorem gInvBasisNhds
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (fun y : M => ∑ k : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChartComponent (I := I) g x₀ i k
          (extChartAt I x₀ y) *
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) y k j) =ᶠ[𝓝 x₀]
      fun _ : M => if i = j then 1 else 0  := by sorry

end Components

end
end DifferentialGeometry.Tensor.Coordinates

