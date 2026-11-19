import dep.DifferentialGeometry.Geometry.Curvature.Riemann.Tensor
import dep.DifferentialGeometry.Geometry.Curvature.Sections.Trace
import dep.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import dep.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Pointwise
import dep.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev SmoothTangentSection :=
  ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)

def rm13RealizesConnection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M)) : Prop :=
  forall (X Y Z : SmoothTangentSection (I := I) (M := M)) (x : M)
    (alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x),
      Rm13 x alpha (vec3 (X x) (Y x) (Z x)) =
        cotangentToDual (I := I) alpha
          ((connectionRiemannCurvatureField (I := I) cov
            (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p)) x)

def rm04RealizesConnection
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M)) : Prop :=
  forall (X Y Z W : SmoothTangentSection (I := I) (M := M)) (x : M),
    Rm04 x (vec4 (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x) ((connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p)) x)


theorem rm04_eq_of_realizes [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {A B : Tensor04Section (I := I) (M := M)}
    (hA : rm04RealizesConnection (I := I) g cov A)
    (hB : rm04RealizesConnection (I := I) g cov B)
    (x : M) :
    A x = B x  := by sorry

def ricciTensorRealizesRm13Trace
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M)) : Prop :=
  forall x : M, Ric x = ricciFromRm13At (I := I) (M := M) (Rm13 x)


def ricciTensorRealizesRm04TraceInFrame
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  DifferentialGeometry.Geometry.Curvature.ricciRealizesRm04TraceInFrame (I := I)
    (tensor02ToField (I := I) Ric) (tensor04ToField (I := I) Rm04) gInv frame


def scalarSectionRealizesRicciTraceInFrame
    {Idx : Type*} [Fintype Idx]
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame (I := I)
    scalar (tensor02ToField (I := I) Ric) gInv frame


theorem rm04_comp_eq_connection
    {Idx : Type*}
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : rm04RealizesConnection (I := I) g cov Rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) Rm04 (fun i y => frame i y) x a b c d =
      g.inner x (frame d x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame a y) (fun y => frame b y) (fun y => frame c y)) x)  := by sorry

theorem ricciComp_eq_trace
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : ricciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    (x : M) (i j : Idx) :
    ricciComp (I := I) Ric frame x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * rm04Comp (I := I) Rm04 frame x k i j l  := by sorry

theorem scalarSection_eq_trace
    {Idx : Type*} [Fintype Idx]
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : scalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    (x : M) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciComp (I := I) Ric frame x i j  := by sorry

theorem rm13_comp_eq_connection
    {Idx : Type*} {u : Set M}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hframe : IsLocalFrameOn I E ∞ (fun i y => frame i y) u)
    (hRm : rm13RealizesConnection (I := I) cov Rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) Rm13 (fun i y => frame i y) hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x)  := by sorry

namespace CurvatureSections

theorem rm13_comp_eq_connection
    {Idx : Type*} {u : Set M}
    (K : CurvatureSections (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hframe : IsLocalFrameOn I E ∞ (fun i y => frame i y) u)
    (hRm : rm13RealizesConnection (I := I) cov K.rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) K.rm13 (fun i y => frame i y) hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x)  := by sorry

theorem rm04_comp_eq_connection
    {Idx : Type*}
    (K : CurvatureSections (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : rm04RealizesConnection (I := I) g cov K.rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) K.rm04 (fun i y => frame i y) x a b c d =
      g.inner x (frame d x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame a y) (fun y => frame b y) (fun y => frame c y)) x)  := by sorry

theorem ricci_comp_eq_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureSections (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : ricciTensorRealizesRm04TraceInFrame (I := I) K.ricci K.rm04 gInv frame)
    (x : M) (i j : Idx) :
    ricciComp (I := I) K.ricci frame x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * rm04Comp (I := I) K.rm04 frame x k i j l  := by sorry

theorem ricci_comp_eq_connection_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureSections (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : rm04RealizesConnection (I := I) g cov K.rm04)
    (hRic : ricciTensorRealizesRm04TraceInFrame (I := I) K.ricci K.rm04 gInv
      (fun i y => frame i y))
    (x : M) (i j : Idx) :
    ricciComp (I := I) K.ricci (fun i y => frame i y) x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          g.inner x (frame l x) ((connectionRiemannCurvatureField (I := I) cov
            (fun y => frame k y) (fun y => frame i y) (fun y => frame j y)) x)  := by sorry

theorem scalar_eq_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureSections (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : scalarSectionRealizesRicciTraceInFrame (I := I) K.scalar K.ricci gInv frame)
    (x : M) :
    K.scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciComp (I := I) K.ricci frame x i j  := by sorry

end CurvatureSections

section Producers

variable [T2Space M]

structure ConnectionCurvatureSections
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) where
  rm13 : Tensor13Section (I := I) (M := M)
  rm04 : Tensor04Section (I := I) (M := M)
  ricci : Tensor02Section (I := I) (M := M)
  rm13Realizes : rm13RealizesConnection (I := I) cov rm13
  rm04Realizes : rm04RealizesConnection (I := I) g cov rm04
  ricciRealizes : ricciTensorRealizesRm13Trace (I := I) ricci rm13

theorem rm13Section_realizes
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) :
    rm13RealizesConnection (I := I) cov
      (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.rm13Section (I := I) (M := M)
        cov hcov)  := by sorry

theorem rm04Section_realizes
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) :
    rm04RealizesConnection (I := I) g cov
      (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.rm04Section (I := I) g cov
        hcov)  := by sorry

end Producers

end DifferentialGeometry.Geometry.Curvature

