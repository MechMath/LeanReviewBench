import dep.DifferentialGeometry.Geometry.Curvature.Riemann.Tensor
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import dep.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Mixed
import dep.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option autoImplicit false

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type _} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CovariantDerivative

noncomputable def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x
    ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x v) p

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem tangentConstAt_self (x : M) (v : TangentSpace I x) :
    tangentConstAt (I := I) x v x = v  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem mdifferentiableAt_tangentConstAt_self
    (x : M) (v : TangentSpace I x) :
    MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p)) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem tangentConstAt_add (x : M) (v w : TangentSpace I x) :
    (tangentConstAt (I := I) x (v + w) : (p : M) → TangentSpace I p) =
      (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p) +
        tangentConstAt (I := I) x w  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem tangentConstAt_smul (x : M) (a : Real) (v : TangentSpace I x) :
    (tangentConstAt (I := I) x (a • v) : (p : M) → TangentSpace I p) =
      a • (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p)  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_tangentConst_apply_mdiffAt_self
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (v w : TangentSpace I x) :
    MDiffAt
      (T% (fun p : M => (cov (tangentConstAt (I := I) x v) p)
        (tangentConstAt (I := I) x w p))) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_smooth_apply_mdiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    MDiffAt (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_smooth_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_smooth_apply_raw_mdiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    {X : (p : M) → TangentSpace I p}
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (hX : MDiffAt (T% X) x) :
    MDiffAt (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x  := by sorry

omit [FiniteDimensional ℝ E] in
theorem curvField_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M =>
        connectionRiemannCurvatureField cov
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem metric_inner_contMDiffAt
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) → TangentSpace I p} {x : M} {n : WithTop ℕ∞}
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% Y) x)
    (hn : n ≤ ∞) :
    ContMDiffAt I 𝓘(Real, Real) n
      (fun y : M => g.inner y (X y) (Y y)) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem metric_inner_contMDiffOn_frame
    (g : SmoothRiemannianMetric I M)
    {u : Set M} {Idx : Type*}
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x : M => g.inner x (frame i x) (frame j x)) u  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_tangentConst_add_apply_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (v₁ v₂ w : TangentSpace I x) :
    ∀ᶠ p in 𝓝 x,
      (cov (tangentConstAt (I := I) x (v₁ + v₂)) p)
          (tangentConstAt (I := I) x w p) =
      (cov (tangentConstAt (I := I) x v₁) p) (tangentConstAt (I := I) x w p) +
        (cov (tangentConstAt (I := I) x v₂) p) (tangentConstAt (I := I) x w p)  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_tangentConst_smul_apply_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (a : Real) (v w : TangentSpace I x) :
    ∀ᶠ p in 𝓝 x,
      (cov (tangentConstAt (I := I) x (a • v)) p)
          (tangentConstAt (I := I) x w p) =
        a • (cov (tangentConstAt (I := I) x v) p) (tangentConstAt (I := I) x w p)  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem connectionRiemannCurvatureField_congr_of_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X X' Y Y' Z Z' :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hX : (fun p : M => X p) =ᶠ[𝓝 x] fun p : M => X' p)
    (hY : (fun p : M => Y p) =ᶠ[𝓝 x] fun p : M => Y' p)
    (hZ : (fun p : M => Z p) =ᶠ[𝓝 x] fun p : M => Z' p) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z' p) x  := by sorry

omit [FiniteDimensional ℝ E] in
theorem connectionRiemannCurvatureField_tensorial_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    TensorialAt I E
      (fun X : (p : M) → TangentSpace I p =>
        connectionRiemannCurvatureField cov X
          (fun p : M => Y p) (fun p : M => Z p) x) x  := by sorry

omit [FiniteDimensional ℝ E] in
theorem connectionRiemannCurvatureField_tensorial_middle
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    TensorialAt I E
      (fun Y : (p : M) → TangentSpace I p =>
        connectionRiemannCurvatureField cov
          (fun p : M => X p) Y (fun p : M => Z p) x) x  := by sorry

theorem connectionRiemannCurvatureField_congr_first_two_point
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X X' Y Y' Z :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hX : X x = X' x) (hY : Y x = Y' x) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z p) x  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem connectionRiemannCurvatureField_smul_right_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {f : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (x : M) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p)
        (fun p : M => f p • Z p) x =
      f x • connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p)
        (fun p : M => Z p) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem connectionRiemannCurvatureField_add_right_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z Z' :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p)
        (fun p : M => (Z + Z') p) x =
      connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p)
          (fun p : M => Z p) x +
        connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p)
          (fun p : M => Z' p) x  := by sorry

omit [CompleteSpace E] in
private theorem smooth_linear_tangentSection_pointwise
    [T2Space M]
    {x : M}
    (Φ :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) →
        TangentSpace I x)
    (hadd : ∀ σ τ, Φ (σ + τ) = Φ σ + Φ τ)
    (hsmul : ∀ (f : C^∞⟮I, M; Real⟯) σ, Φ (f • σ) = f x • Φ σ)
    {σ τ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)}
    (hστ : σ x = τ x) :
    Φ σ = Φ τ  := by sorry

theorem connectionRiemannCurvatureField_congr_point
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    [T2Space M]
    (X X' Y Y' Z Z' :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hX : X x = X' x) (hY : Y x = Y' x) (hZ : Z x = Z' x) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z' p) x  := by sorry

end CovariantDerivative

end DifferentialGeometry.Geometry.Curvature

