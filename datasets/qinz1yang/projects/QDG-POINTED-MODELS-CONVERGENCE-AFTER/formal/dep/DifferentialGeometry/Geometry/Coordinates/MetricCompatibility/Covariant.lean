import dep.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}


def InverseMetricComponentsForMetricInFrameOn [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x i j,
    (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, metricCompForMetricInFrame (I := I) g frame x i k * gInv x k j) =
        (if i = j then 1 else 0)


omit [FiniteDimensional ℝ E] in
theorem gInvForMetric_symm [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame) :
    forall x i j, gInv x i j = gInv x j i  := by sorry

def inverseMetricCovDerivForMetricCompInFrame
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d k l : Idx) : Real :=
  mvfderiv (I := I) (fun y : M => gInv y k l) x (frame d x) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a k * gInv x a l) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a l * gInv x k a)

def inverseMetricCovDerivForMetricCompAlongInFrame
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (k l : Idx) : Real :=
  mvfderiv (I := I) (fun y : M => gInv y k l) x X +
    (∑ a : Idx,
      christoffelAlongInFrame cov frame hframe x X a k * gInv x a l) +
    (∑ a : Idx,
      christoffelAlongInFrame cov frame hframe x X a l * gInv x k a)

omit [FiniteDimensional ℝ E] [Fintype Idx] in
private theorem metric_localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x  := by sorry

omit [FiniteDimensional ℝ E] [Fintype Idx] in
theorem metricComp_mdiffAt
    (g : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i j : Idx) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y i j) x  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricCompForMetricInFrame_mvfderiv_eq_christoffel
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    mvfderiv (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x (frame d x) =
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d a p *
          metricCompForMetricInFrame (I := I) g frame x p b) +
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d b p *
          metricCompForMetricInFrame (I := I) g frame x a p)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricComp_extDeriv_tangent
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (X : TangentSpace I x) (a b : Idx) :
    mvfderiv (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x X =
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x X a p *
          metricCompForMetricInFrame (I := I) g frame x p b) +
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x X b p *
          metricCompForMetricInFrame (I := I) g frame x a p)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricCompForMetricInFrame_mvfderiv_eq_christoffelAlong
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a b : Idx) :
    mvfderiv (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x (X x) =
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) a p *
          metricCompForMetricInFrame (I := I) g frame x p b) +
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) b p *
          metricCompForMetricInFrame (I := I) g frame x a p)  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mdiffAt_finset_sum_real
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_finset_sum_real
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    mvfderiv (I := I) (t.sum f) x v =
      t.sum (fun i => mvfderiv (I := I) (f i) x v)  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_mul_real
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    mvfderiv (I := I) (fun y : M => f y * g y) x v =
      f x * mvfderiv (I := I) g x v +
        mvfderiv (I := I) f x v * g x  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem deriv_congr_nhds
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    mvfderiv (I := I) f x v = mvfderiv (I := I) g x v  := by sorry

theorem inverseMetric_derivative_solve
    [DecidableEq Idx]
    (metric ric gInv gInvDt : Idx -> Idx -> Real)
    (i : Idx)
    (hrow : forall j : Idx,
      (∑ a : Idx,
        (gInvDt i a * metric a j + gInv i a * ((-2 : Real) * ric a j))) = 0)
    (hleft : forall a b : Idx,
      (∑ k : Idx, gInv a k * metric k b) = (if a = b then 1 else 0))
    (hright : forall a b : Idx,
      (∑ k : Idx, metric a k * gInv k b) = (if a = b then 1 else 0))
    (hmetric_symm : forall a b : Idx, metric a b = metric b a)
    (j : Idx) :
    gInvDt i j =
      2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem inverseMetricCovDerivForMetricCompInFrame_eq_zero
    [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b) x)
    (d k l : Idx) :
    inverseMetricCovDerivForMetricCompInFrame (I := I) gInv cov frame hframe x d k l = 0  := by sorry

omit [FiniteDimensional ℝ E] in
theorem inverseMetricCovDerivForMetricCompAlongInFrame_eq_zero
    [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b) x)
    (k l : Idx) :
    inverseMetricCovDerivForMetricCompAlongInFrame
        (I := I) gInv cov frame hframe x (X x) k l = 0  := by sorry

end Components

end
end DifferentialGeometry.Tensor.Coordinates

