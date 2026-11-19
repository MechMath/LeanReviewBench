import dep.DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import dep.DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import dep.DifferentialGeometry.Geometry.Metric.Family.Basic
import dep.DifferentialGeometry.Geometry.Operator.Scalar.Calculus

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Geometry.Curvature

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

def gradientAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : TangentSpace I x :=
  gradientFun (I := I) (G.metric t) f x

def divergenceAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x) (x : M) : Real :=
  divergence (I := I) (G.connection t) X x

def laplacianAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : Real :=
  laplacian (I := I) (G.connection t) (G.metric t) f x

def driftTerm
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (f : M -> Real) (x : M) : Real :=
  (G.metric t).inner x (X x) (gradientAt (I := I) G t f x)

def heatOperatorWithDrift
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (f : M -> Real) (x : M) : Real :=
  laplacianAt (I := I) G t f x + driftTerm (I := I) G t X f x

def heatOperator
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : Real :=
  laplacianAt (I := I) G t f x

@[simp] theorem driftTerm_zero_drift
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    driftTerm (I := I) G t (fun y : M => (0 : TangentSpace I y)) f x = 0  := by sorry

@[simp] theorem heatOperator_eq_laplacianAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    heatOperator (I := I) G t f x = laplacianAt (I := I) G t f x  := by sorry

theorem heatOperatorWithDrift_zero_drift
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    heatOperatorWithDrift (I := I) G t
        (fun y : M => (0 : TangentSpace I y)) f x =
      heatOperator (I := I) G t f x  := by sorry

section FamilyAlgebraicRules

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_sub_const
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} (c : Real) {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X (fun y : M => f y - c) x =
      driftTerm (I := I) G t X f x  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_const_smul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (a : Real) {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X (a • f) x =
      a * driftTerm (I := I) G t X f x  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_add
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    driftTerm (I := I) G t X (fun y : M => f y + h y) x =
      driftTerm (I := I) G t X f x +
        driftTerm (I := I) G t X h x  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_sub
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    driftTerm (I := I) G t X (fun y : M => f y - h y) x =
      driftTerm (I := I) G t X f x -
        driftTerm (I := I) G t X h x  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem heatOperatorWithDrift_sub_const
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} (c : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (x : M) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y - c) x =
      heatOperatorWithDrift (I := I) G t X f x  := by sorry

theorem heatOperatorWithDrift_const_smul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    heatOperatorWithDrift (I := I) G t X (a • f) x =
      a * heatOperatorWithDrift (I := I) G t X f x  := by sorry

theorem laplacianAt_sub
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    laplacianAt (I := I) G t (fun y : M => f y - h y) x =
      laplacianAt (I := I) G t f x -
        laplacianAt (I := I) G t h x  := by sorry

theorem laplacianAt_sub_at
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    laplacianAt (I := I) G t (fun y : M => f y - h y) x =
      laplacianAt (I := I) G t f x -
        laplacianAt (I := I) G t h x  := by sorry

theorem heatOperatorWithDrift_sub_at
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y - h y) x =
      heatOperatorWithDrift (I := I) G t X f x -
        heatOperatorWithDrift (I := I) G t X h x  := by sorry

theorem laplacianAt_smul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t (a • f) x =
      a * laplacianAt (I := I) G t f x  := by sorry

theorem laplacianAt_add
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    laplacianAt (I := I) G t (fun y : M => f y + h y) x =
      laplacianAt (I := I) G t f x +
        laplacianAt (I := I) G t h x  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem gradientAt_mul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientAt (I := I) G t (fun y : M => f y * h y) x =
      f x • gradientAt (I := I) G t h x +
        h x • gradientAt (I := I) G t f x  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_mul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    driftTerm (I := I) G t X (fun y : M => f y * h y) x =
      f x * driftTerm (I := I) G t X h x +
        h x * driftTerm (I := I) G t X f x  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem gradientAt_rpow
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M} (p : Real)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    gradientAt (I := I) G t (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) • gradientAt (I := I) G t f x  := by sorry

theorem laplacianAt_mul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x)
    (hfgradh : MDiffAt (T% (f • fun y : M =>
      gradientFun (I := I) (G.metric t) h y)) x)
    (hhgradf : MDiffAt (T% (h • fun y : M =>
      gradientFun (I := I) (G.metric t) f y)) x) :
    laplacianAt (I := I) G t (fun y : M => f y * h y) x =
      f x * laplacianAt (I := I) G t h x +
        h x * laplacianAt (I := I) G t f x +
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t h x)  := by sorry

theorem laplacianAt_mul_of_scalarRegular
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) f z) y)
    (hgradh : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) h z) y) :
    laplacianAt (I := I) G t (fun y : M => f y * h y) x =
      f x * laplacianAt (I := I) G t h x +
        h x * laplacianAt (I := I) G t f x +
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t h x)  := by sorry

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem heatDrift_comp
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {φ : Real -> Real} {f : M -> Real} {x : M}
    (hφ : Differentiable Real φ)
    (hφ' : DifferentiableAt Real (deriv φ) (f x))
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    heatOperatorWithDrift (I := I) G t X
        (fun y : M => φ (f y)) x =
      deriv φ (f x) * heatOperatorWithDrift (I := I) G t X f x +
        deriv (deriv φ) (f x) *
          (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t f x)  := by sorry

theorem heatDrift_mul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) f z) y)
    (hgradh : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) h z) y) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y * h y) x =
      f x * heatOperatorWithDrift (I := I) G t X h x +
        h x * heatOperatorWithDrift (I := I) G t X f x +
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t h x)  := by sorry

theorem heatDrift_add
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y + h y) x =
      heatOperatorWithDrift (I := I) G t X f x +
        heatOperatorWithDrift (I := I) G t X h x  := by sorry

theorem laplacianAt_rpow
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M} (p : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : forall y : M, 0 < f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) * laplacianAt (I := I) G t f x +
        (p * (p - 1) * f x ^ (p - 2)) *
          (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t f x)  := by sorry

theorem laplacianAt_sq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hfg : MDiffAt (T% (f • fun y : M =>
      gradientFun (I := I) (G.metric t) f y)) x) :
    laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t f x)
          (gradientAt (I := I) G t f x)  := by sorry

theorem laplacianAt_sq_of_scalarRegular
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : ∀ y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) f z) y) :
    laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t f x)
          (gradientAt (I := I) G t f x)  := by sorry

end FamilyAlgebraicRules

@[simp] theorem gradientAt_eq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    gradientAt (I := I) G t f x = gradientFun (I := I) (G.metric t) f x  := by sorry

omit [FiniteDimensional ℝ E] in
@[simp] theorem divergenceAt_eq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x) (x : M) :
    divergenceAt (I := I) G t X x =
      divergence (I := I) (G.connection t) X x  := by sorry

@[simp] theorem laplacianAt_eq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    laplacianAt (I := I) G t f x =
      laplacian (I := I) (G.connection t) (G.metric t) f x  := by sorry

theorem driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X f x = 0  := by sorry

theorem driftTerm_eq_zero_at_spatial_min
    [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X f x = 0  := by sorry

def laplacianNonnegativeAtSpatialMinFamily
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time,
    LaplacianNonnegativeAtSpatialMin (I := I) (G.connection t) (G.metric t)

theorem laplacian_nonnegative_at_spatial_min_family
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time) :
    laplacianNonnegativeAtSpatialMinFamily (I := I) G  := by sorry

theorem laplacianAt_nonpos_at_spatial_max
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hmax : IsLocalMax f x)
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    laplacianAt (I := I) G t f x <= 0  := by sorry

theorem laplacianAt_smul_at
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (a : Real) {f : M → Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t (a • f) x = a * laplacianAt (I := I) G t f x  := by sorry

theorem laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M → Real} {x : M}
    (hmax : IsLocalMax f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t f x ≤ 0  := by sorry

theorem heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) f y) x) :
    0 <= heatOperatorWithDrift (I := I) G t X f x  := by sorry

theorem heatOperatorWithDrift_at_spatial_min_nonneg
    [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) f y) x) :
    0 <= heatOperatorWithDrift (I := I) G t X f x  := by sorry

end

end DifferentialGeometry.Geometry.Curvature

