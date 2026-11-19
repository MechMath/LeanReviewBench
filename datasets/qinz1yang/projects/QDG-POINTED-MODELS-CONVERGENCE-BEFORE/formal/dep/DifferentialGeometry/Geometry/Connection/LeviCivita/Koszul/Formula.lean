import dep.DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import dep.DifferentialGeometry.Geometry.Operator.Family.Basic
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import dep.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Basic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)

def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x
    ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x v) p

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tangentConstAt_apply (x : M) (v : TangentSpace I x) (p : M) :
    tangentConstAt (I := I) x v p =
      TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x v) p  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tangentConstAt_self (x : M) (v : TangentSpace I x) :
    tangentConstAt (I := I) x v x = v  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tangentConstAt_add (x : M) (v w : TangentSpace I x) :
    (tangentConstAt (I := I) x (v + w) : (p : M) -> TangentSpace I p) =
      (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p) +
        tangentConstAt (I := I) x w  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tangentConstAt_smul (x : M) (a : Real) (v : TangentSpace I x) :
    (tangentConstAt (I := I) x (a • v) : (p : M) -> TangentSpace I p) =
      a • (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p)  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem mdifferentiableAt_tangentConstAt_self
    (x : M) (v : TangentSpace I x) :
    MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p)) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mdifferentiableAt_metric_inner
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt (fun y : M => g.inner y (X y) (Y y)) x  := by sorry

def directionalDerivAlong
    (X : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M) : Real :=
  mvfderiv (I := I) f x (X x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] theorem directionalDerivAlong_add_left
    (X X' : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M) :
  directionalDerivAlong (I := I) (X + X') f x =
      directionalDerivAlong (I := I) X f x +
        directionalDerivAlong (I := I) X' f x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] theorem directionalDerivAlong_smul_left
    (a : Real) (X : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M) :
  directionalDerivAlong (I := I) (a • X) f x =
      a * directionalDerivAlong (I := I) X f x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
private theorem directionalDerivAlong_add_fun
    (X : (p : M) -> TangentSpace I p) {f h : M -> Real} (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    directionalDerivAlong (I := I) X (f + h) x =
      directionalDerivAlong (I := I) X f x +
        directionalDerivAlong (I := I) X h x  := by sorry

def koszulScalar
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M) : Real :=
  directionalDerivAlong (I := I) X (fun y : M => g.inner y (Y y) (Z y)) x +
    directionalDerivAlong (I := I) Y (fun y : M => g.inner y (Z y) (X y)) x -
    directionalDerivAlong (I := I) Z (fun y : M => g.inner y (X y) (Y y)) x -
    g.inner x (X x) (VectorField.mlieBracket I Y Z x) +
    g.inner x (Y x) (VectorField.mlieBracket I Z X x) +
    g.inner x (Z x) (VectorField.mlieBracket I X Y x)

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_add_first
    (g : SmoothRiemannianMetric I M)
    (X X' Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g (X + X') Y Z x =
      koszulScalar (I := I) g X Y Z x +
        koszulScalar (I := I) g X' Y Z x  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_add_second
    (g : SmoothRiemannianMetric I M)
    (X Y Y' Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g X (Y + Y') Z x =
      koszulScalar (I := I) g X Y Z x +
        koszulScalar (I := I) g X Y' Z x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
private theorem mvfderiv_mul_at
    {f h : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    mvfderiv (I := I) (fun y : M => f y * h y) x v =
      f x * mvfderiv (I := I) h x v +
        mvfderiv (I := I) f x v * h x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
private theorem directionalDerivAlong_mul_fun
    (X : (p : M) -> TangentSpace I p) {f h : M -> Real} (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    directionalDerivAlong (I := I) X (fun y : M => f y * h y) x =
      f x * directionalDerivAlong (I := I) X h x +
        directionalDerivAlong (I := I) X f x * h x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
private theorem directionalDerivAlong_smul_fun_left
    {f : M -> Real} (X : (p : M) -> TangentSpace I p) (h : M -> Real) (x : M) :
    directionalDerivAlong (I := I) (f • X) h x =
      f x * directionalDerivAlong (I := I) X h x  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_smul_first
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g (f • X) Y Z x =
      f x * koszulScalar (I := I) g X Y Z x  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_smul_second
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g X (f • Y) Z x =
      f x * koszulScalar (I := I) g X Y Z x +
        (2 * directionalDerivAlong (I := I) X f x) *
          g.inner x (Y x) (Z x)  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_add_third
    (g : SmoothRiemannianMetric I M)
    (X Y Z Z' : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    koszulScalar (I := I) g X Y (Z + Z') x =
      koszulScalar (I := I) g X Y Z x +
        koszulScalar (I := I) g X Y Z' x  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_smul_third
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g X Y (f • Z) x =
      f x * koszulScalar (I := I) g X Y Z x  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_tensorial_first
    (g : SmoothRiemannianMetric I M)
    (Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X : (p : M) -> TangentSpace I p =>
      koszulScalar (I := I) g X Y Z x) x  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_tensorial_third
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z : (p : M) -> TangentSpace I p =>
      koszulScalar (I := I) g X Y Z x) x  := by sorry

def koszulCovectorField
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) :
    Module.Dual Real (TangentSpace I x) :=
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
    ((1 / 2 : Real) *
      koszulScalar (I := I) g X Y (tangentConstAt (I := I) x (B i)) x) •
        (B.coord i)


def koszulNablaField
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (koszulCovectorField (I := I) g X Y x)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem koszulNablaField_inner_eq_covector
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (Z : TangentSpace I x) :
    g.inner x (koszulNablaField (I := I) g X Y x) Z =
      koszulCovectorField (I := I) g X Y x Z  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulCovectorField_smul_first
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulCovectorField (I := I) g (f • X) Y x =
      f x • koszulCovectorField (I := I) g X Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulCovectorField_add_first
    (g : SmoothRiemannianMetric I M)
    (X X' Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) :
    koszulCovectorField (I := I) g (X + X') Y x =
      koszulCovectorField (I := I) g X Y x +
        koszulCovectorField (I := I) g X' Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_smul_first
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulNablaField (I := I) g (f • X) Y x =
      f x • koszulNablaField (I := I) g X Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_add_first
    (g : SmoothRiemannianMetric I M)
    (X X' Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) :
    koszulNablaField (I := I) g (X + X') Y x =
      koszulNablaField (I := I) g X Y x +
        koszulNablaField (I := I) g X' Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulCovectorField_add_second
    (g : SmoothRiemannianMetric I M)
    (X Y Y' : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    koszulCovectorField (I := I) g X (Y + Y') x =
      koszulCovectorField (I := I) g X Y x +
        koszulCovectorField (I := I) g X Y' x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_add_second
    (g : SmoothRiemannianMetric I M)
    (X Y Y' : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    koszulNablaField (I := I) g X (Y + Y') x =
      koszulNablaField (I := I) g X Y x +
        koszulNablaField (I := I) g X Y' x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metric_inner_sum_basis_coord
    (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x))
    (Y v : TangentSpace I x) :
    (∑ i, g.inner x Y (B i) * (B.coord i) v) = g.inner x Y v  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulCovectorField_smul_second
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulCovectorField (I := I) g X (f • Y) x =
      f x • koszulCovectorField (I := I) g X Y x +
        directionalDerivAlong (I := I) X f x • metricFlatLinear (I := I) g x (Y x)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_smul_second
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulNablaField (I := I) g X (f • Y) x =
      f x • koszulNablaField (I := I) g X Y x +
        directionalDerivAlong (I := I) X f x • Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_tensorial_first
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun X : (p : M) -> TangentSpace I p =>
      koszulNablaField (I := I) g X Y x) x  := by sorry

def koszulNablaAt
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (v : TangentSpace I x) : TangentSpace I x :=
  koszulNablaField (I := I) g (tangentConstAt (I := I) x v) Y x

def KoszulCovectorCorrectAt
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) : Prop :=
  forall Z : (p : M) -> TangentSpace I p,
    MDiffAt (T% Z) x ->
      koszulCovectorField (I := I) g X Y x (Z x) =
        (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulCovectorField_apply_of_mdiff
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    koszulCovectorField (I := I) g X Y x (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulCovectorCorrectAt_of_mdiff
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    KoszulCovectorCorrectAt (I := I) g X Y x  := by sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaField_eval_of_covector_correct
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hcorrect : KoszulCovectorCorrectAt (I := I) g X Y x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x (koszulNablaField (I := I) g X Y x) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaField_inner_eq_koszulScalar
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x (koszulNablaField (I := I) g X Y x) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulScalar_pair_sum
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M) :
    (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x +
      (1 / 2 : Real) * koszulScalar (I := I) g X Z Y x =
        directionalDerivAlong (I := I) X (fun y : M => g.inner y (Y y) (Z y)) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulScalar_swap_sub
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M) :
    (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x -
      (1 / 2 : Real) * koszulScalar (I := I) g Y X Z x =
        g.inner x (VectorField.mlieBracket I X Y x) (Z x)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaField_eq_of_first_eq_at
    (g : SmoothRiemannianMetric I M)
    (X X' Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x)
    (hxx : X x = X' x) :
    koszulNablaField (I := I) g X Y x =
      koszulNablaField (I := I) g X' Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaAt_eq_of_extension
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) (hXx : X x = v) :
    koszulNablaAt (I := I) g Y x v =
      koszulNablaField (I := I) g X Y x  := by sorry

def leviCivitaConnectionAt
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x := by
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  let W : Fin (Module.finrank Real (TangentSpace I x)) -> TangentSpace I x := fun i =>
    koszulNablaField (I := I) g (tangentConstAt (I := I) x (B i)) Y x
  exact LinearMap.toContinuousLinearMap
    (B.constr Real W)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem leviCivitaConnectionAt_apply_basis
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (i : Fin (Module.finrank Real (TangentSpace I x))) :
    leviCivitaConnectionAt (I := I) g Y x
        ((Module.finBasis Real (TangentSpace I x)) i) =
      koszulNablaField (I := I) g
        (tangentConstAt (I := I) x ((Module.finBasis Real (TangentSpace I x)) i)) Y x  := by sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionAt_basis_agreesWithField
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (i : Fin (Module.finrank Real (TangentSpace I x))) :
    leviCivitaConnectionAt (I := I) g Y x
        ((Module.finBasis Real (TangentSpace I x)) i) =
      koszulNablaAt (I := I) g Y x
        ((Module.finBasis Real (TangentSpace I x)) i)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionAt_agreesWithField
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    leviCivitaConnectionAt (I := I) g Y x (X x) =
      koszulNablaField (I := I) g X Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionAt_agreesWithDescended
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    leviCivitaConnectionAt (I := I) g Y x v =
      koszulNablaAt (I := I) g Y x v  := by sorry

def leviCivitaConnectionOfMetric
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) where
  toFun := fun Y x => leviCivitaConnectionAt (I := I) g Y x
  isCovariantDerivativeOnUniv := by
    refine
      { add := ?_
        leibniz := ?_ }
    · intro Y Y' x hY hY' _hx
      ext v
      rw [add_apply]
      rw [leviCivitaConnectionAt_agreesWithDescended
        (I := I) g (Y + Y') x (mdifferentiableAt_add_section hY hY') v]
      rw [leviCivitaConnectionAt_agreesWithDescended
        (I := I) g Y x hY v]
      rw [leviCivitaConnectionAt_agreesWithDescended
        (I := I) g Y' x hY' v]
      unfold koszulNablaAt
      exact koszulNablaField_add_second (I := I) g
        (tangentConstAt (I := I) x v) Y Y' x
        (mdifferentiableAt_tangentConstAt_self (I := I) x v) hY hY'
    · intro Y f x hY hf _hx
      ext v
      rw [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [leviCivitaConnectionAt_agreesWithDescended
        (I := I) g (f • Y) x (hf.smul_section hY) v]
      rw [leviCivitaConnectionAt_agreesWithDescended
        (I := I) g Y x hY v]
      unfold koszulNablaAt
      rw [koszulNablaField_smul_second (I := I) g
        (tangentConstAt (I := I) x v) Y x hf
        (mdifferentiableAt_tangentConstAt_self (I := I) x v) hY]
      congr 1
      unfold directionalDerivAlong
      rw [tangentConstAt_self]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem leviCivitaConnectionOfMetric_apply
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M) :
    leviCivitaConnectionOfMetric (I := I) g Y x =
      leviCivitaConnectionAt (I := I) g Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_apply_descended
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    leviCivitaConnectionOfMetric (I := I) g Y x v =
      koszulNablaAt (I := I) g Y x v  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_inner_eq_koszulScalar_tangent
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) :
    g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) v =
      (1 / 2 : Real) *
        koszulScalar (I := I) g X Y (tangentConstAt (I := I) x v) x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_isMetricCompatible
    (g : SmoothRiemannianMetric I M) :
    IsMetricCompatible (I := I) (leviCivitaConnectionOfMetric (I := I) g) g  := by sorry

end

end DifferentialGeometry.Geometry.Connection

