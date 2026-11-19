import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
open DifferentialGeometry.Geometry.Curvature

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

omit [FiniteDimensional ℝ E] in
theorem invCovZeroLocal
    [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M}
    (hinvX : ∀ i j : Idx,
      (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx, metricCompForMetricInFrame (I := I) g frame x i k * gInv x k j) =
          (if i = j then 1 else 0))
    (hinvN : ∀ i j : Idx,
      (fun y : M => ∑ k : Idx,
          gInv y i k * metricCompForMetricInFrame (I := I) g frame y k j) =ᶠ[𝓝 x]
        fun _ : M => if i = j then 1 else 0)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (hu : IsOpen u) (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b) x)
    (k l : Idx) :
    inverseMetricCovDerivForMetricCompAlongInFrame
        (I := I) gInv cov frame hframe x (X x) k l = 0  := by sorry

theorem gInvCovZeroAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (x₀ : M) (k l : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricCovDerivForMetricCompAlongInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChartComponent (I := I) g x₀ a b
            (extChartAt I x₀ y))
        cov (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        x₀ (X x₀) k l = 0  := by sorry

end Components

end
end DifferentialGeometry.Tensor.Coordinates

