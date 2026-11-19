import Mathlib.Tactic
import dep.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import dep.DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import dep.DifferentialGeometry.Geometry.Metric.Basic
import dep.DifferentialGeometry.Analysis.TimeInterval
import dep.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import dep.DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import dep.DifferentialGeometry.Geometry.Metric.QuadraticBounds.TimeSlab
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
open DifferentialGeometry.Geometry.Curvature


set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

structure MetricConnectionFamily (Time : Type*) where
  metric : Time -> SmoothRiemannianMetric I M
  connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  metricCompatible : forall t : Time,
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) (connection t)
      (metric t)

structure MetricConnectionFamilyOn (D : RealTimeInterval) where
  metric : Real -> SmoothRiemannianMetric I M
  connection : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  metricCompatible : forall t : RealTimeInterval.FlowTime D,
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I)
      (connection (t : Real)) (metric (t : Real))

namespace MetricConnectionFamily

def restrict
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (D : RealTimeInterval) :
    MetricConnectionFamilyOn (I := I) (M := M) D where
  metric := G.metric
  connection := G.connection
  metricCompatible := fun t => G.metricCompatible (t : Real)

@[simp] theorem restrict_metric
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (D : RealTimeInterval) (t : Real) :
    (G.restrict D).metric t = G.metric t  := by sorry

@[simp] theorem restrict_connection
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (D : RealTimeInterval) (t : Real) :
    (G.restrict D).connection t = G.connection t  := by sorry

end MetricConnectionFamily

namespace MetricConnectionFamilyOn


def toFlowTimeFamily
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) :
    MetricConnectionFamily (I := I) (M := M) (RealTimeInterval.FlowTime D) where
  metric := fun t => G.metric (t : Real)
  connection := fun t => G.connection (t : Real)
  metricCompatible := fun t => G.metricCompatible t


def toRegularTimeFamily
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) :
    MetricConnectionFamily (I := I) (M := M) (RealTimeInterval.RegularTime D) where
  metric := fun t => G.metric (t : Real)
  connection := fun t => G.connection (t : Real)
  metricCompatible := fun t => G.metricCompatible (RealTimeInterval.regularToFlow t)


def metricAt
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    SmoothRiemannianMetric I M :=
  G.metric (t : Real)


def connectionAt
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  G.connection (t : Real)

@[simp] theorem metricAt_eq
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    G.metricAt t = G.metric (t : Real)  := by sorry

@[simp] theorem connectionAt_eq
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    G.connectionAt t = G.connection (t : Real)  := by sorry

theorem metricCompatibleAt
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) (G.connectionAt t)
      (G.metricAt t)  := by sorry

theorem metricCompatibleAt_regular
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) :
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I)
      (G.connection (t : Real)) (G.metric (t : Real))  := by sorry

end MetricConnectionFamilyOn

section IntervalSmoothness

variable [FiniteDimensional Real E]

def tensor0SFamilyContinuousOnSet
    (s : Nat) (K : Set Real)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    Prop :=
  Continuous (fun q : {t : Real // t ∈ K} × M =>
    TotalSpace.mk' (Tensor0SModel s Real E)
      (E := fun x : M => Tensor0SSpace s I x) q.2 (A q.1.1 q.2))

abbrev SmoothTwoTensorFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 2

structure SmoothTwoTensorFamilyOnSet
    (K : Set Real) (A : SmoothTwoTensorFamily (I := I) (M := M)) : Prop where
  coeff :
    ∀ (x : M) (X Y : TangentSpace I x),
      ContDiffOn Real ⊤
        (fun t : Real => A t x (fun i : Fin 2 => if i = 0 then X else Y)) K
  tensor_cont :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => A t x)

namespace tensor0SFamilyContinuousOnSet


theorem mono
    {s : Nat} {K L : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s L A)
    (hKL : K ⊆ L) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A  := by sorry

theorem comp_time
    {s : Nat} {K L : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s L A)
    {φ : Real -> Real} (hφ : Continuous φ) (hmaps : Set.MapsTo φ K L) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => A (φ t) x)  := by sorry

theorem of_union_closedOpen
    {s : Nat} {a c b : Real} (hac : a < c)
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (h1 : tensor0SFamilyContinuousOnSet (I := I) (M := M) s (Set.Ico a c) A)
    (h2 : tensor0SFamilyContinuousOnSet (I := I) (M := M) s (Set.Ioo a b) A) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s (Set.Ico a b) A  := by sorry

theorem congr
    {s : Nat} {K : Set Real}
    {A B : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    (hAB : ∀ t ∈ K, ∀ x : M, A t x = B t x) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K B  := by sorry

theorem const_smul
    {s : Nat} {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (c : Real)
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => c • A t x)  := by sorry

theorem add
    {s : Nat} {K : Set Real}
    {A B : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    (hB : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K B) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => A t x + B t x)  := by sorry

theorem smul
    {s : Nat} {K : Set Real}
    {f : Real -> M -> Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hf : Continuous (fun q : {t : Real // t ∈ K} × M => f q.1.1 q.2))
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) s K
      (fun t x => f t x • A t x)  := by sorry

theorem tangentBundle
    {s : Nat} {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel s Real E)
        (E := fun x : M => Tensor0SSpace s I x) q.2.proj
        (A q.1.1 q.2.proj))  := by sorry

theorem eval_continuous
    {s : Nat} {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K A)
    {P : Type*} [TopologicalSpace P]
    {τ : P -> Real} {b : P -> M}
    (hτ : Continuous τ) (hτK : ∀ p : P, τ p ∈ K)
    (hb : Continuous b)
    {v : Fin s -> (p : P) -> TangentSpace I (b p)}
    (hv : ∀ i : Fin s, Continuous (fun p : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p))) :
    Continuous (fun p : P => A (τ p) (b p) (fun i : Fin s => v i p))  := by sorry

end tensor0SFamilyContinuousOnSet

theorem tensor0SFamily_quadCont
    {K : Set Real}
    {A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x}
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K A) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      quad02 (I := I) (M := M) (A q.1.1 q.2.proj) q.2.2)  := by sorry

structure MetricFamilySmoothOn
    (D : RealTimeInterval)
    (g_fam : ℝ → SmoothRiemannianMetric I M) : Prop where
  coeff :
    forall (x : M) (X Y : TangentSpace I x),
    ContDiffOn Real ∞ (fun t : Real => (g_fam t).inner x X Y) D.regular
  coeff_cont :
    forall (x : M) (X Y : TangentSpace I x),
    ContinuousOn (fun t : Real => (g_fam t).inner x X Y) D.carrier
  metricTensor_cont :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => metricTensorField (I := I) (g_fam t) x)
  frameCompSmooth :
    forall {Idx : Type} [Fintype Idx]
      (frame : Idx -> (x : M) -> TangentSpace I x) {u : Set M},
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u ->
      forall i j : Idx,
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            (g_fam p.1).inner p.2 (frame i p.2) (frame j p.2))
          (D.regular ×ˢ u)


theorem metric_smooth_coeff_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (x : M) (X Y : TangentSpace I x) :
    ContDiffOn Real ∞ (fun t : Real => (g_fam t).inner x X Y) D.regular  := by sorry

theorem metric_coeff_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (x : M) (X Y : TangentSpace I x) :
    ContinuousOn (fun t : Real => (g_fam t).inner x X Y) D.carrier  := by sorry

theorem metricTensor_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => metricTensorField (I := I) (g_fam t) x)  := by sorry

theorem metricTensor_cont_restrict_of_metricFamilySmoothOn
    {D : RealTimeInterval} {K : Set Real}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (hK : K ⊆ D.carrier) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (g_fam t) x)  := by sorry

theorem metricTensor_tangentBundle_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval} {K : Set Real}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (hK : K ⊆ D.carrier) :
    Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
        (metricTensorField (I := I) (g_fam q.1.1) q.2.proj))  := by sorry

theorem metricTimeBundleQuad_cont_of_metricFamilySmoothOn
    {D : RealTimeInterval} {K : Set Real}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (hK : K ⊆ D.carrier) :
    Continuous
      (metricTimeBundleQuad (I := I) (M := M) g_fam K)  := by sorry

noncomputable def metricCoeff
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (x : M) (X Y : TangentSpace I x) : Real -> Real :=
  fun t => (g_fam t).inner x X Y

omit [FiniteDimensional ℝ E] in
@[simp] theorem metricCoeff_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (x : M) (X Y : TangentSpace I x) (t : Real) :
    metricCoeff g_fam x X Y t = (g_fam t).inner x X Y  := by sorry

end IntervalSmoothness

end DifferentialGeometry.Geometry.Curvature

