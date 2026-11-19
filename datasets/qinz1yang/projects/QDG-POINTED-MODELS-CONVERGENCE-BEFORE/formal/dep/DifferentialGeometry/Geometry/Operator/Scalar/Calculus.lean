import dep.DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import dep.DifferentialGeometry.Geometry.Metric.Basic
import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import dep.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Mixed
import dep.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import dep.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace

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
variable {Time : Type*}

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)

def metricFlatEquiv (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  metricFlatMap (I := I) g x

@[simp] theorem metricFlatEquiv_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatEquiv (I := I) g x v w = g.inner x v w  := by sorry

theorem metricSharp_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : Module.Dual Real (TangentSpace I x)) :
    metricSharp (I := I) g x alpha =
      (metricFlatEquiv (I := I) g x).symm alpha  := by sorry

def gradientFun (g : SmoothRiemannianMetric I M) (f : M -> Real) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (mvfderiv (I := I) f x).toLinearMap

@[simp] theorem gradientFun_eq
    (g : SmoothRiemannianMetric I M) (f : M -> Real) (x : M) :
    gradientFun (I := I) g f x =
      metricSharp (I := I) g x (mvfderiv (I := I) f x).toLinearMap  := by sorry

theorem inner_gradientFun
    (g : SmoothRiemannianMetric I M) (f : M -> Real) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradientFun (I := I) g f x) v =
      mvfderiv (I := I) f x v  := by sorry

theorem gradientFun_eq_of_flat
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    {v : TangentSpace I x}
    (hf : (mvfderiv (I := I) f x).toLinearMap =
      metricFlatEquiv (I := I) g x v) :
    gradientFun (I := I) g f x = v  := by sorry

theorem gradientFun_eq_zero_of_mfderiv_eq_zero
    (g : SmoothRiemannianMetric I M) (f : M -> Real) {x : M}
    (hf : mfderiv I 𝓘(Real, Real) f x = 0) :
    gradientFun (I := I) g f x = 0  := by sorry

theorem gradientFun_eq_zero_of_isLocalMin
    [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0  := by sorry

theorem gradientFun_eq_zero_of_isLocalMax
    [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmax : IsLocalMax f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0  := by sorry

theorem gradientFun_const
    (g : SmoothRiemannianMetric I M) (c : Real) (x : M) :
    gradientFun (I := I) g (fun _ : M => c) x = 0  := by sorry

theorem gradientFun_const_smul
    (g : SmoothRiemannianMetric I M) (a : Real)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (a • f) x =
      a • gradientFun (I := I) g f x  := by sorry

theorem gradientFun_neg
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (-f) x =
      -gradientFun (I := I) g f x  := by sorry

theorem gradientFun_add
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientFun (I := I) g (fun y : M => f y + h y) x =
      gradientFun (I := I) g f x + gradientFun (I := I) g h x  := by sorry

theorem gradientFun_sum {κ : Type*}
    (g : SmoothRiemannianMetric I M) (s : Finset κ)
    {f : κ -> M -> Real} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    gradientFun (I := I) g (∑ i ∈ s, f i) x =
      ∑ i ∈ s, gradientFun (I := I) g (f i) x  := by sorry

theorem gradientFun_sum_smul {κ : Type*}
    (g : SmoothRiemannianMetric I M) (s : Finset κ) (c : κ -> Real)
    {f : κ -> M -> Real} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    gradientFun (I := I) g (∑ i ∈ s, c i • f i) x =
      ∑ i ∈ s, c i • gradientFun (I := I) g (f i) x  := by sorry

theorem gradientFun_sub
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientFun (I := I) g (fun y : M => f y - h y) x =
      gradientFun (I := I) g f x - gradientFun (I := I) g h x  := by sorry

theorem gradientFun_comp
    (g : SmoothRiemannianMetric I M)
    {φ : Real -> Real} {f : M -> Real} {x : M}
    (hφ : DifferentiableAt Real φ (f x))
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (fun y : M => φ (f y)) x =
      deriv φ (f x) • gradientFun (I := I) g f x  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_mul
    {f h : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    mvfderiv (I := I) (fun y : M => f y * h y) x v =
      f x * mvfderiv (I := I) h x v +
        mvfderiv (I := I) f x v * h x  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_const_mul_apply
    (a : Real) {f : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    mvfderiv (I := I) (fun y : M => a * f y) x v =
      a * mvfderiv (I := I) f x v  := by sorry

theorem gradientFun_mul
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientFun (I := I) g (fun y : M => f y * h y) x =
      f x • gradientFun (I := I) g h x +
        h x • gradientFun (I := I) g f x  := by sorry

theorem gradientFun_pow
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (n : Nat)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (fun y : M => f y ^ (n + 1)) x =
      (((n + 1 : Nat) : Real) * f x ^ n) •
        gradientFun (I := I) g f x  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_rpow
    {f : M -> Real} {x : M} (p : Real) (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    mvfderiv (I := I) (fun y : M => f y ^ p) x v =
      (p * f x ^ (p - 1)) * mvfderiv (I := I) f x v  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mdifferentiableAt_rpow
    {f : M -> Real} {x : M} (p : Real)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    MDifferentiableAt I 𝓘(Real, Real) (fun y : M => f y ^ p) x  := by sorry

theorem gradientFun_rpow
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (p : Real)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    gradientFun (I := I) g (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) • gradientFun (I := I) g f x  := by sorry

theorem gradientFun_log
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    gradientFun (I := I) g (fun y : M => Real.log (f y)) x =
      (f x)⁻¹ • gradientFun (I := I) g f x  := by sorry

theorem gradientFun_mul_self
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (fun y : M => f y * f y) x =
      (2 * f x) • gradientFun (I := I) g f x  := by sorry

def divergence
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x : M) : Real :=
  LinearMap.trace Real (TangentSpace I x) (cov X x).toLinearMap

omit [FiniteDimensional ℝ E] in
@[simp] theorem divergence_eq
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x : M) :
    divergence (I := I) cov X x =
      LinearMap.trace Real (TangentSpace I x) (cov X x).toLinearMap  := by sorry

def laplacian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (x : M) : Real :=
  divergence (I := I) cov (gradientFun (I := I) g f) x

@[simp] theorem laplacian_eq
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (x : M) :
    laplacian (I := I) cov g f x =
      divergence (I := I) cov (gradientFun (I := I) g f) x  := by sorry

section AlgebraicRules

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

omit [FiniteDimensional ℝ E] in
theorem divergence_zero
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) :
    divergence (I := I) cov (0 : (x : M) -> TangentSpace I x) x = 0  := by sorry

omit [FiniteDimensional ℝ E]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem divergence_add
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (_hVB : VectorBundle ℝ E (TangentSpace I : M → Type _))
    {X Y : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    divergence (I := I) cov (X + Y) x =
      divergence (I := I) cov X x + divergence (I := I) cov Y x  := by sorry

omit [FiniteDimensional ℝ E]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem divergence_const_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (_hVB : VectorBundle ℝ E (TangentSpace I : M → Type _))
    (a : Real) {X : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) :
    divergence (I := I) cov (a • X) x =
      a * divergence (I := I) cov X x  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem divergence_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (_hVB : VectorBundle ℝ E (TangentSpace I : M → Type _))
    {f : M -> Real} {X : (x : M) -> TangentSpace I x} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) :
    divergence (I := I) cov (f • X) x =
      f x * divergence (I := I) cov X x +
        mvfderiv (I := I) f x (X x)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem divergence_sub
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {X Y : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    divergence (I := I) cov (X - Y) x =
      divergence (I := I) cov X x - divergence (I := I) cov Y x  := by sorry

theorem laplacian_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) (c : Real) (x : M) :
    laplacian (I := I) cov g (fun _ : M => c) x = 0  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_add_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (c : Real) {f : M -> Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => c + f y) x =
      laplacian (I := I) cov g f x  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_sub_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (c : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (x : M) :
    laplacian (I := I) cov g (fun y : M => f y - c) x =
      laplacian (I := I) cov g f x  := by sorry

theorem laplacian_sub
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x) :
    laplacian (I := I) cov g (fun y : M => f y - h y) x =
      laplacian (I := I) cov g f x -
        laplacian (I := I) cov g h x  := by sorry

theorem laplacian_add_at
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M → Real} {x : M}
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt
      (T% fun y : M => gradientFun (I := I) g h y) x) :
    laplacian (I := I) cov g (fun y : M => f y + h y) x =
      laplacian (I := I) cov g f x +
        laplacian (I := I) cov g h x  := by sorry

theorem laplacian_sub_at
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x) :
    laplacian (I := I) cov g (fun y : M => f y - h y) x =
      laplacian (I := I) cov g f x -
        laplacian (I := I) cov g h x  := by sorry

theorem laplacian_const_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (a • f) x =
      a * laplacian (I := I) cov g f x  := by sorry

theorem laplacian_smul_at
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    (a : Real) {f : M → Real} {x : M}
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (a • f) x =
      a * laplacian (I := I) cov g f x  := by sorry

theorem divergence_smul_gradientFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    divergence (I := I) cov (f • fun y : M => gradientFun (I := I) g f y) x =
      f x * laplacian (I := I) cov g f x +
        g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x)  := by sorry

theorem divergence_smul_gradientFun_pair
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x) :
    divergence (I := I) cov (f • fun y : M => gradientFun (I := I) g h y) x =
      f x * laplacian (I := I) cov g h x +
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g h x)  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_comp_of_eventually_differentiable
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {phi : Real → Real} {f : M → Real} {x : M}
    (hphi : ∀ᶠ z in nhds (f x), DifferentiableAt ℝ phi z)
    (hphi' : DifferentiableAt Real (deriv phi) (f x))
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => phi (f y)) x =
      deriv phi (f x) * laplacian (I := I) cov g f x +
        deriv (deriv phi) (f x) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x)  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_comp
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {φ : Real -> Real} {f : M -> Real} {x : M}
    (hφ : Differentiable Real φ)
    (hφ' : DifferentiableAt Real (deriv φ) (f x))
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => φ (f y)) x =
      deriv φ (f x) * laplacian (I := I) cov g f x +
        deriv (deriv φ) (f x) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x)  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_comp_at
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {phi : Real → Real} {f : M → Real} {x : M}
    (hphi : Differentiable Real phi)
    (hphi' : DifferentiableAt Real (deriv phi) (f x))
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => phi (f y)) x =
      deriv phi (f x) * laplacian (I := I) cov g f x +
        deriv (deriv phi) (f x) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x)  := by sorry

theorem laplacian_mul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x)
    (hfgradh : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g h y)) x)
    (hhgradf : MDiffAt
      (T% (h • fun y : M => gradientFun (I := I) g f y)) x) :
    laplacian (I := I) cov g (fun y : M => f y * h y) x =
      f x * laplacian (I := I) cov g h x +
        h x * laplacian (I := I) cov g f x +
          2 * g.inner x
            (gradientFun (I := I) g f x)
            (gradientFun (I := I) g h x)  := by sorry

theorem laplacian_mul_at
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M → Real} {x : M}
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt
      (T% fun y : M => gradientFun (I := I) g h y) x) :
    laplacian (I := I) cov g (fun y : M => f y * h y) x =
      f x * laplacian (I := I) cov g h x +
        h x * laplacian (I := I) cov g f x +
          2 * g.inner x
            (gradientFun (I := I) g f x)
            (gradientFun (I := I) g h x)  := by sorry

theorem laplacian_rpow_at
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (p : Real)
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : 0 < f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) * laplacian (I := I) cov g f x +
        (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x)  := by sorry

theorem laplacian_rpow
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (p : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : forall y : M, 0 < f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) * laplacian (I := I) cov g f x +
        (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x)  := by sorry

theorem laplacian_log
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : forall y : M, 0 < f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => Real.log (f y)) x =
      (f x)⁻¹ * laplacian (I := I) cov g f x -
        (f x ^ 2)⁻¹ *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x)  := by sorry

theorem half_laplacian_mul_self_eq_divergence_smul_gradientFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hfg : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g f y)) x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (fun y : M => f y * f y) x =
      divergence (I := I) cov
        (f • fun y : M => gradientFun (I := I) g f y) x  := by sorry

theorem half_laplacian_mul_self
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hfg : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g f y)) x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (fun y : M => f y * f y) x =
      f x * laplacian (I := I) cov g f x +
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g f x)  := by sorry

end AlgebraicRules

end

end DifferentialGeometry.Geometry.Operator

