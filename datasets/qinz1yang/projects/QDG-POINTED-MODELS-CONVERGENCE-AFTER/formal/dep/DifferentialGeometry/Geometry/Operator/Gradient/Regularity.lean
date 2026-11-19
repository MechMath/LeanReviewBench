import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Coordinate
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import dep.DifferentialGeometry.Geometry.Connection.LocalFrameRegularity

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradientFun_coeff_eq_sum
    (g : SmoothRiemannianMetric I M) (f : M -> Real)
    {x₀ y : M} (hy : y ∈ coordinateFrameSet (I := I) x₀)
    (k : CoordinateIdx (𝕜 := Real) E) :
    (coordinateFrameAt_isLocalFrame (I := I) x₀).coeff k y
        (gradientFun (I := I) g f y) =
      ∑ l : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
            (extChartAt I x₀ y) *
          mvfderiv (I := I) f y (coordinateFrameAt (I := I) x₀ l y)  := by sorry

theorem gradientFun_contMDiffAt
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x₀) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (T% fun y : M => gradientFun (I := I) g f y) x₀  := by sorry

theorem gradientFun_contMDiffAt_one
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) 2 f x₀) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) 1
      (T% fun y : M => gradientFun (I := I) g f y) x₀  := by sorry

theorem gradientFun_smooth
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (T% fun y : M => gradientFun (I := I) g f y)  := by sorry

theorem gradientFun_mdiffOn
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f U)
    {x : M} (hx : x ∈ U) :
    MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x  := by sorry

theorem gradientFun_mdiffAt
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x : M) :
    MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x  := by sorry

theorem laplacian_congr_of_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) {f h : M → Real} {x : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x)
    (hh : ContMDiffAt I 𝓘(Real, Real) ∞ h x)
    (heq : f =ᶠ[nhds x] h) :
    laplacian (I := I) cov g f x = laplacian (I := I) cov g h x  := by sorry

theorem laplacian_sub_at_of_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M → Real} {x : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x)
    (hh : ContMDiffAt I 𝓘(Real, Real) ∞ h x) :
    laplacian (I := I) cov g (fun y : M ↦ f y - h y) x =
      laplacian (I := I) cov g f x - laplacian (I := I) cov g h x  := by sorry

theorem grad_comp_mdiffAt
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {φ : Real → Real} {f : M → Real} {x : M}
    (hφ : Differentiable Real φ)
    (hφ' : DifferentiableAt Real (deriv φ) (f x))
    (hf : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    MDiffAt
      (T% fun y : M =>
        gradientFun (I := I) g (fun z => φ (f z)) y) x  := by sorry

theorem scalar_mul_grad_mdiffAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : ∀ y : M,
      MDiffAt (T% fun z : M => gradientFun (I := I) g f z) y) :
    MDiffAt (T% (f • fun y : M => gradientFun (I := I) g f y)) x  := by sorry

theorem mdiffAt_smul_gradientFun
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : ∀ y : M,
      MDiffAt (T% fun z : M => gradientFun (I := I) g f z) y) :
    MDiffAt (T% (f • fun y : M => gradientFun (I := I) g f y)) x  := by sorry

theorem mdiffAt_const_mul_sub_const_smul_gradientFun
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (a c : Real)
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    MDiffAt
      (T% ((fun y : M => a * (f y - c)) • fun y : M =>
        gradientFun (I := I) g (fun z : M => a * (f z - c)) y)) x  := by sorry

theorem mdifferentiableAt_gradientFun_finset_sum
    (g : SmoothRiemannianMetric I M) {κ : Type*}
    (s : Finset κ) (u : κ → M → ℝ) (x : M)
    (hu : ∀ i ∈ s, ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u i) y)
    (hgrad : ∀ i ∈ s, MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y : M => gradientFun (I := I) g (u i) y) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y : M => gradientFun (I := I) g (fun z => ∑ i ∈ s, u i z) y) x  := by sorry

theorem mdifferentiableAt_gradientFun_mul
    (g : SmoothRiemannianMetric I M) {u v : M → ℝ} {x : M}
    (hus : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) u y)
    (hvs : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) v y)
    (hug : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M => gradientFun g u y) x)
    (hvg : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M => gradientFun g v y) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y : M => gradientFun g (fun z => u z * v z) y) x  := by sorry

theorem mdifferentiableAt_gradientFun_const_mul
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {x : M} (a : ℝ)
    (hus : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) u y)
    (hug : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M => gradientFun g u y) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y : M => gradientFun g (fun z => a * u z) y) x  := by sorry

theorem mdifferentiableAt_gradientFun_add
    (g : SmoothRiemannianMetric I M) {u v : M → ℝ} {x : M}
    (hus : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) u y)
    (hvs : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) v y)
    (hug : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M => gradientFun g u y) x)
    (hvg : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M => gradientFun g v y) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y : M => gradientFun g (fun z => u z + v z) y) x  := by sorry

end DifferentialGeometry.Geometry.Operator

