import dep.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import dep.DifferentialGeometry.Geometry.Coordinates.Connection.Christoffel
import dep.DifferentialGeometry.Geometry.Coordinates.Frame.Coordinate
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
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

omit [SigmaCompactSpace M] [T2Space M] in
theorem torsion_free_at_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {x : M}
    (htf : IsTorsionFreeAt (I := I) cov x)
    {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem torsion_free_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : IsTorsionFree (I := I) cov)
    {x : M} {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) - cov X x (Y x) = VectorField.mlieBracket I X Y x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem torsion_free_family_apply
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (htf : IsTorsionFreeFamilyOn (I := I) G)
    (t : RealTimeInterval.FlowTime D)
    {x : M} {X Y : (p : M) -> TangentSpace I p}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    G.connectionAt t Y x (X x) - G.connectionAt t X x (Y x) =
      VectorField.mlieBracket I X Y x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem coordinate_basis_coord_eq_sum_inv_metric_inner
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (a : Idx) (V : TangentSpace I x) :
    basis.coord a V =
      ∑ k : Idx, gInv a k * g.inner x (basis k) V  := by sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulScalar_coordinateFrame_eq_metric_derivs_of_mem
    (g : SmoothRiemannianMetric I M)
    (x0 : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x0)
    (i j l : CoordinateIdx (𝕜 := Real) E) :
    koszulScalar (I := I) g
        (coordinateFrameAt (I := I) x0 i)
        (coordinateFrameAt (I := I) x0 j)
        (coordinateFrameAt (I := I) x0 l) x =
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
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
            (coordinateFrameAt (I := I) x0 j y)) x  := by sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_coordinateFrame_eq_metric_derivs
    (g : SmoothRiemannianMetric I M)
    (x0 : M) (i j l : CoordinateIdx (𝕜 := Real) E) :
    koszulScalar (I := I) g
        (coordinateFrameAt (I := I) x0 i)
        (coordinateFrameAt (I := I) x0 j)
        (coordinateFrameAt (I := I) x0 l) x0 =
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x0 j y)
            (coordinateFrameAt (I := I) x0 l y)) x0 +
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 j)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x0 i y)
            (coordinateFrameAt (I := I) x0 l y)) x0 -
      directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 l)
        (fun y : M =>
          g.inner y (coordinateFrameAt (I := I) x0 i y)
            (coordinateFrameAt (I := I) x0 j y)) x0  := by sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulScalar_coordinateFrame_symm
    (g : SmoothRiemannianMetric I M)
    (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E)
    (Z : (p : M) -> TangentSpace I p) :
    (1 / 2 : Real) *
        koszulScalar (I := I) g (coordinateFrameAt (I := I) x0 i)
          (coordinateFrameAt (I := I) x0 j) Z x0 =
      (1 / 2 : Real) *
        koszulScalar (I := I) g (coordinateFrameAt (I := I) x0 j)
          (coordinateFrameAt (I := I) x0 i) Z x0  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem coordinate_torsion_coeff_eq_christoffel_skew
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x0 : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff k x0
        (cov.torsion x0
          (coordinateFrameAt (I := I) x0 i x0)
          (coordinateFrameAt (I := I) x0 j x0)) =
      christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
          (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k -
        christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
          (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 j i k  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem coordinate_christoffel_symm_of_torsionFree
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htf : IsTorsionFree (I := I) cov)
    (x0 : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k =
      christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 j i k  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_coordinateFrame_apply_symm
    (g : SmoothRiemannianMetric I M) (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    (leviCivitaConnectionOfMetric (I := I) g
        (coordinateFrameAt (I := I) x0 j) x0)
        (coordinateFrameAt (I := I) x0 i x0) =
        (leviCivitaConnectionOfMetric (I := I) g
        (coordinateFrameAt (I := I) x0 i) x0)
        (coordinateFrameAt (I := I) x0 j x0)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_coordinate_christoffel_symm
    (g : SmoothRiemannianMetric I M) (x0 : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k =
      christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 j i k  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_coordinate_christoffel_formula
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hinv : MetricInverseInBasis (I := I) g x0
      (coordinateFrameAtToBasis (I := I) x0) gInv)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) x0 i j k =
      (1 / 2 : Real) *
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv k l *
            (directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 i)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 j y)
                    (coordinateFrameAt (I := I) x0 l y)) x0 +
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 j)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 l y)) x0 -
              directionalDerivAlong (I := I) (coordinateFrameAt (I := I) x0 l)
                (fun y : M =>
                  g.inner y (coordinateFrameAt (I := I) x0 i y)
                    (coordinateFrameAt (I := I) x0 j y)) x0)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_coordinate_torsion_basis_zero
    (g : SmoothRiemannianMetric I M) (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    (leviCivitaConnectionOfMetric (I := I) g).torsion x0
        (coordinateFrameAt (I := I) x0 i x0)
        (coordinateFrameAt (I := I) x0 j x0) = 0  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_isTorsionFree
    (g : SmoothRiemannianMetric I M) :
    IsTorsionFree (I := I) (leviCivitaConnectionOfMetric (I := I) g)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_isLeviCivita
    (g : SmoothRiemannianMetric I M) :
    IsLeviCivita (I := I) (leviCivitaConnectionOfMetric (I := I) g) g  := by sorry

end DifferentialGeometry.Geometry.Connection

