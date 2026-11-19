import dep.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import dep.DifferentialGeometry.Geometry.Metric.Pullback.Basic
import dep.DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
import dep.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.TotalNabla0S
import dep.DifferentialGeometry.Bundle.Frame
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedManifoldMetricConvergence

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M]

noncomputable def metricCovDerivStep
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 3) := by
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_regularity (E := E) (H := H)
      (I := I) (M := M) (a + 2) cov hcov A
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cov, hcov, hreg]
    using
      Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (a + 2) cov A hreg

noncomputable def metricCovDeriv
    (h gRef : SmoothRiemannianMetric I M) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    (by
      have : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        change IsManifold I ∞ M
        infer_instance
      exact Tensor0SBundle.metricTensorField (I := I) (M := M) h)
    (fun a A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          metricCovDerivStep (I := I) gRef a A)

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_apply_section
    (h gRef : SmoothRiemannianMetric I M)
    (X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) (slots : Fin 2 -> TangentSpace I x) :
    metricCovDeriv (I := I) h gRef 1 x (Fin.cons (X x) slots) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        X (metricCovDeriv (I := I) h gRef 0) x slots  := by sorry

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_eval_smooth_slots
    (h gRef : SmoothRiemannianMetric I M)
    (X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (X x) (fun a : Fin 2 => V a x)) =
      mvfderiv (I := I)
          (fun p : M => h.inner p (V 0 p) (V 1 p)) x (X x) -
        ∑ a : Fin 2,
          h.inner x
            ((Function.update (fun b : Fin 2 => V b x) a
              (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
                gRef)
                  (fun p : M => V a p) x) (X x))) 0)
            ((Function.update (fun b : Fin 2 => V b x) a
              (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
                gRef)
                  (fun p : M => V a p) x) (X x))) 1)  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] in
private theorem mvfderiv_congr_eventually_real
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    mvfderiv (I := I) f x v = mvfderiv (I := I) g x v  := by sorry

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_eval_localFrame
    {Idx : Type*} {u : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (frame d x)
          (fun q : Fin 2 => if q = 0 then frame a x else frame b x)) =
      mvfderiv (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x)))  := by sorry

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_component_localFrame
    {Idx : Type*} {u : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
        (metricCovDeriv (I := I) h gRef 1 x)
        (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
          Fin 3 -> Idx) =
      mvfderiv (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x)))  := by sorry

end FixedManifoldMetricConvergence

end CheegerGromovCompactness
end DifferentialGeometry

