import dep.DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import dep.DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev RawTangentField :=
  (x : M) -> TangentSpace I x

abbrev RawTwoTensorField :=
  (x : M) -> TangentSpace I x -> TangentSpace I x -> Real

abbrev RawFourTensorField :=
  (x : M) -> TangentSpace I x -> TangentSpace I x -> TangentSpace I x ->
    TangentSpace I x -> Real


abbrev InverseMetricComponents (M : Type*) (Idx : Type*) :=
  M -> Idx -> Idx -> Real

def connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) :
    RawTangentField (I := I) (M := M) :=
  fun x =>
    (cov (fun y => (cov Z y) (Y y)) x) (X x) -
      (cov (fun y => (cov Z y) (X y)) x) (Y x) -
        (cov Z x) (VectorField.mlieBracket I X Y x)


theorem connectionRiemannCurvatureField_swap
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) (x : M) :
    connectionRiemannCurvatureField (I := I) cov Y X Z x =
      -connectionRiemannCurvatureField (I := I) cov X Y Z x  := by sorry

section MetricTrace

variable {Idx : Type*} [Fintype Idx]

def InverseMetricComponentsInFrame [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x i j,
    (∑ k : Idx, gInv x i k * g.inner x (frame k x) (frame j x)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (frame i x) (frame k x) * gInv x k j) =
        (if i = j then 1 else 0)


theorem invComp_symm [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrame (I := I) g gInv frame) :
    forall x i j, gInv x i j = gInv x j i  := by sorry

def ricciFromRiemann04TraceInFrame
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    RawTwoTensorField (I := I) (M := M) :=
  fun x X Y =>
    ∑ k : Idx, ∑ l : Idx, gInv x k l * Riemann04 x (frame k x) X Y (frame l x)

omit [IsManifold I ∞ M] in
@[simp]
theorem ricciFromRiemann04TraceInFrame_apply
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (X Y : TangentSpace I x) :
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame x X Y =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Riemann04 x (frame k x) X Y (frame l x)  := by sorry

def scalarFromRicciTraceInFrame
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : M -> Real :=
  fun x => ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x)

omit [IsManifold I ∞ M] in
@[simp]
theorem scalarFromRicciTraceInFrame_apply
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) (x : M) :
    scalarFromRicciTraceInFrame (I := I) Ric gInv frame x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x)  := by sorry

end MetricTrace

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Integral.Connection

abbrev InverseMetricComponents :=
  DifferentialGeometry.Geometry.Curvature.InverseMetricComponents

end DifferentialGeometry.Integral.Connection

