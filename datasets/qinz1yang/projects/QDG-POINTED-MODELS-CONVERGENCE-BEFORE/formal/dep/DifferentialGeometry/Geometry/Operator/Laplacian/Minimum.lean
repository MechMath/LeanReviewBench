import dep.DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.DerivativeTest

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Operator

noncomputable section


open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)

private noncomputable def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x
    ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x v) p

omit [FiniteDimensional ℝ E] in
@[simp] private theorem tangentConstAt_self (x : M) (v : TangentSpace I x) :
    tangentConstAt (I := I) x v x = v  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem mdifferentiableAt_tangentConstAt_self
    (x : M) (v : TangentSpace I x) :
    MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p)) x  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem tangent_continuousLinearMapAt_self (x : M) :
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x =
      (1 : E →L[Real] E)  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem writtenInExtChartAt_real_eq
    (f : M → Real) (x : M) :
    writtenInExtChartAt I 𝓘(Real, Real) x f =
      fun y : E => f ((extChartAt I x).symm y)  := by sorry

private theorem deriv_deriv_nonneg_of_isLocalMin
    {φ : Real -> Real} {t₀ : Real}
    (hmin : IsLocalMin φ t₀)
    (hcont : ContinuousAt φ t₀) :
    0 <= deriv (deriv φ) t₀  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem fderiv_fderiv_apply_self_nonneg_of_isLocalMin_model
    {F : E -> Real} {y : E}
    (hmin : IsLocalMin F y)
    (hF : DifferentiableAt Real F y)
    (hF_near : ∀ᶠ z in nhds y, DifferentiableAt Real F z)
    (v : E) :
    0 <= fderiv Real (fun z : E => fderiv Real F z v) y v  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem writtenInExtChartAt_differentiableAt_of_mdifferentiableAt
    {f : M -> Real} {x p : M} {z : E}
    (hp : p ∈ (chartAt H x).source)
    (hp_interior : I.IsInteriorPoint p)
    (hz : z ∈ (extChartAt I x).target)
    (hpz : p = (extChartAt I x).symm z)
    (h : MDifferentiableAt I 𝓘(Real, Real) f p) :
    DifferentiableAt Real (writtenInExtChartAt I 𝓘(Real, Real) x f) z  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem mvfderiv_tangentConstAt_eq_fderiv_writtenInExtChartAt
    {f : M -> Real} {x p : M}
    (hp : p ∈ (chartAt H x).source)
    (hp_interior : I.IsInteriorPoint p)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f p)
    (v : TangentSpace I x) :
    mvfderiv (I := I) f p (tangentConstAt (I := I) x v p) =
      fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f) (extChartAt I x p)
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x v)  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mfderiv_eq_zero_at_spatial_min_of_isInteriorPoint
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    mfderiv I 𝓘(Real, Real) f x = 0  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mfderiv_eq_zero_at_spatial_min
    [I.Boundaryless]
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    mfderiv I 𝓘(Real, Real) f x = 0  := by sorry

theorem gradientFun_eq_zero_at_spatial_min_of_isInteriorPoint
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0  := by sorry

theorem gradientFun_eq_zero_at_spatial_min
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0  := by sorry

def LaplacianNonnegativeAtSpatialMin
    [hVectorBundle : VectorBundle Real E (TangentSpace I : M -> Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop := by
  let _ := hVectorBundle
  exact forall {f : M -> Real} {x : M},
    IsLocalMin f x ->
      MDifferentiableAt I 𝓘(Real, Real) f x ->
        (∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y) ->
        MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x ->
          0 <= laplacian (I := I) cov g f x

theorem divergence_eq_of_section_eq_zero
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {X : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hzero : X x = 0) :
    divergence (I := I) cov X x = divergence (I := I) cov' X x  := by sorry

theorem laplacian_eq_laplacian_of_gradient_eq_zero
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    (hgradSec : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgrad : gradientFun (I := I) g f x = 0) :
    laplacian (I := I) cov g f x = laplacian (I := I) cov' g f x  := by sorry

private theorem fderiv_fderiv_self_nonneg_of_isLocalMin
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (_hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (v : TangentSpace I x) :
    0 <=
      mvfderiv (I := I)
        (fun y : M =>
          mvfderiv (I := I) f y
            (tangentConstAt (I := I) x v y)) x v  := by sorry

theorem cov_gradientFun_inner_self_nonneg_at_spatial_min_of_isInteriorPoint
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (v : TangentSpace I x) :
    0 <=
      g.inner x
        ((cov (fun y : M => gradientFun (I := I) g f y) x) v) v  := by sorry

theorem laplacian_nonneg_at_spatial_min_of_metricCompatible_of_isInteriorPoint
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
  0 <= laplacian (I := I) cov g f x  := by sorry

theorem laplacian_nonneg_at_spatial_min_of_metricCompatible
    [I.Boundaryless]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
  0 <= laplacian (I := I) cov g f x  := by sorry

theorem laplacianNonnegativeAtSpatialMin_of_metricCompatible
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g) :
    LaplacianNonnegativeAtSpatialMin (I := I) cov g  := by sorry

end

end DifferentialGeometry.Geometry.Operator

