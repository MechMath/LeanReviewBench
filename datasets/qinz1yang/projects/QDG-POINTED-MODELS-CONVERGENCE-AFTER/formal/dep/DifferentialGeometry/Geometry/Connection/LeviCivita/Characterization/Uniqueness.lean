import dep.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import dep.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import dep.DifferentialGeometry.Geometry.Connection.LeviCivita.Characterization.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Connection

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

def LeviCivitaConnectionUniqueOnSmooth
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _),
    CovariantDerivative.ContMDiffCovariantDerivative cov ∞ ->
      CovariantDerivative.ContMDiffCovariantDerivative cov' ∞ ->
        IsLeviCivita (I := I) cov g ->
          IsLeviCivita (I := I) cov' g ->
            forall {x : M} (Y : (p : M) -> TangentSpace I p),
              MDiffAt (T% Y) x ->
                forall v : TangentSpace I x,
                  cov Y x v = cov' Y x v


omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivita_inner_eq_half_koszul
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hlc : IsLeviCivita (I := I) cov g)
    {X Y Z : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x (cov Y x (X x)) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem coordinateFrame_christoffel_formula_point_of_isLeviCivita
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (g : SmoothRiemannianMetric I M)
    (hLC : IsLeviCivita (I := I) cov g)
    (x0 : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x0)
    (gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hinv : MetricInverseInBasis (I := I) g x
      (coordinateFrameAtBasis (I := I) x0 hx) gInv)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x i j k =
      (1 / 2 : Real) *
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv k l *
            (directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 j y)
                    (coordinateFrameAt (I := I) x0 l y)) x +
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 j)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 l y)) x -
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 l)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 j y)) x)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivita_apply_eq_of_smooth
    {cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hcov : IsLeviCivita (I := I) cov g)
    (hcov' : IsLeviCivita (I := I) cov' g)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) = cov' Y x (X x)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivita_apply_eq_of_smooth_direction
    {cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hcov : IsLeviCivita (I := I) cov g)
    (hcov' : IsLeviCivita (I := I) cov' g)
    {x : M} (Y : (p : M) -> TangentSpace I p)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    cov Y x v = cov' Y x v  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionUniqueOnSmooth
    (g : SmoothRiemannianMetric I M) :
    LeviCivitaConnectionUniqueOnSmooth (I := I) g  := by sorry

end DifferentialGeometry.Geometry.Connection

