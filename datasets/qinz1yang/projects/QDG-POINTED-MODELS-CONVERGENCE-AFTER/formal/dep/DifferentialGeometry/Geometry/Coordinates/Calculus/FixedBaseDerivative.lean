import dep.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import dep.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Mixed
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry

theorem mvfderiv_real_eq_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners Real E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> Real) (x : M) (V : TangentSpace I x) :
    mvfderiv (I := I) f x V =
      NormedSpace.fromTangentSpace (f x)
        (mfderiv I 𝓘(Real, Real) f x V)  := by sorry

theorem mvfderiv_real_model_eq_fderiv
    (f : Real -> Real) (x : Real)
    (V : TangentSpace 𝓘(Real, Real) x) :
    mvfderiv (I := 𝓘(Real, Real)) f x V =
      fderiv Real f x (NormedSpace.fromTangentSpace x V)  := by sorry

private theorem writtenInExtChartAt_real_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> Real) (x : M) (y : E) :
    writtenInExtChartAt I 𝓘(Real, Real) x f y =
      f ((extChartAt I x).symm y)  := by sorry

theorem mvfderiv_comp_diffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H N]
    (f : N -> Real) (Phi : M ≃ₘ⟮I, I⟯ N) (x : M)
    (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f (Phi x)) :
    mvfderiv (I := I) (fun y : M => f (Phi y)) x v =
      mvfderiv (I := I) f (Phi x) (mfderiv I I (Phi : M -> N) x v)  := by sorry

theorem writtenInExtChartAt_diffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {f : M -> Real} {x p : M} {z : E}
    (hp : p ∈ (chartAt H x).source)
    (hz : z ∈ (extChartAt I x).target)
    (hpz : p = (extChartAt I x).symm z)
    (h : MDifferentiableAt I 𝓘(Real, Real) f p) :
    DifferentiableAt Real (writtenInExtChartAt I 𝓘(Real, Real) x f) z  := by sorry

theorem mvfderiv_tangentConstInChart_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {f : M -> Real} {x p : M}
    (hp : p ∈ (chartAt H x).source)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f p)
    (v : E) :
    mvfderiv (I := I) f p
        (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p) =
      fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f) (extChartAt I x p) v  := by sorry

theorem isLocallyConstant_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {f : M -> Real}
    (hf : MDifferentiable I 𝓘(Real, Real) f)
    (hzero : ∀ x : M, mfderiv I 𝓘(Real, Real) f x = 0) :
    IsLocallyConstant f  := by sorry

theorem mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : M -> Real} {φ : E -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hφ :
      writtenInExtChartAt I 𝓘(Real, Real) x f
        =ᶠ[nhds (extChartAt I x x)] φ)
    (V : TangentSpace I x) :
    mvfderiv (I := I) f x V =
      fderiv Real φ (extChartAt I x x) V  := by sorry

def FixedBaseExtDerivTimeDerivativeOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (timeSet : Set ℝ) (u : Set M)
    (F Ft : ℝ -> M -> ℝ) : Prop :=
  forall (t : ℝ) (x : M), x ∈ u ->
    forall V : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => mvfderiv (I := I) (F s) x V)
        (mvfderiv (I := I) (Ft t) x V)
      timeSet
      t

def FixedBaseExtDerivTimeDerivativeOnRegular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (timeSet regularSet : Set ℝ) (u : Set M)
    (F Ft : ℝ -> M -> ℝ) : Prop :=
  forall (t : ℝ), t ∈ regularSet ->
    forall (x : M), x ∈ u ->
      forall V : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => mvfderiv (I := I) (F s) x V)
          (mvfderiv (I := I) (Ft t) x V)
          timeSet
          t

theorem fixedBaseExtDerivTimeDerivativeOn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h : FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u F Ft)
    {t : ℝ} {x : M} (hx : x ∈ u) (V : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => mvfderiv (I := I) (F s) x V)
      (mvfderiv (I := I) (Ft t) x V)
      timeSet
      t  := by sorry

theorem fixedBaseExtDerivTimeDerivativeOnRegular_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h :
      FixedBaseExtDerivTimeDerivativeOnRegular
        (I := I) timeSet regularSet u F Ft)
    {t : ℝ} (ht : t ∈ regularSet) {x : M} (hx : x ∈ u)
    (V : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => mvfderiv (I := I) (F s) x V)
      (mvfderiv (I := I) (Ft t) x V)
      timeSet
      t  := by sorry

theorem FixedBaseExtDerivTimeDerivativeOn.toRegular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set ℝ} {u : Set M}
    {F Ft : ℝ -> M -> ℝ}
    (h : FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet u F Ft) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft  := by sorry

theorem fixedBaseExtDerivTimeDerivativeOn_singleton_of_chart_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M) F Ft  := by sorry

theorem fixedBaseExtDerivTimeDerivativeOnRegular_singleton_of_chart_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real,
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft  := by sorry

theorem fixedBaseExtDerivTimeDerivativeOnRegular_singleton_of_chart_contDiffOnTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hΦ : ContDiff Real 2 (fun p : Real × E => Φ p.1 p.2))
    (hFdiff :
      ∀ s : Real, s ∈ timeSet ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real, s ∈ timeSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, t ∈ regularSet ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real, t ∈ regularSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft  := by sorry

theorem eventuallyEq_timeFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {timeSet : Set Real}
    {Φ Ψ : Real -> E -> Real}
    {t : Real} {y₀ : E}
    (htime : timeSet ∈ 𝓝 t)
    (hdiff : ∀ᶠ y in 𝓝 y₀,
      DifferentiableAt Real
        (fun p : Real × E => Φ p.1 p.2)
        (t, y))
    (hderiv : ∀ᶠ y in 𝓝 y₀,
      HasDerivWithinAt
        (fun s : Real => Φ s y)
        (Ψ t y)
        timeSet
        t) :
    Ψ t =ᶠ[𝓝 y₀]
      fun y : E =>
        (fderiv Real
          (fun p : Real × E => Φ p.1 p.2)
          (t, y)) (1, 0)  := by sorry

theorem fixedBaseAtRegularity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {x₀ : M}
    {F Ft : Real -> M -> Real} {Φ : Real -> E -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hΦ : ∀ t : Real, t ∈ regularSet ->
      ContDiffAt Real 2 (fun p : Real × E => Φ p.1 p.2)
        (t, extChartAt I x₀ x₀))
    (hFdiff :
      ∀ s : Real, s ∈ timeSet ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x₀)
    (hFchart :
      ∀ s : Real, s ∈ timeSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (F s)
          =ᶠ[nhds (extChartAt I x₀ x₀)] Φ s)
    (hFtdiff :
      ∀ t : Real, t ∈ regularSet ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x₀)
    (hFtchart :
      ∀ t : Real, t ∈ regularSet ->
        writtenInExtChartAt I 𝓘(Real, Real) x₀ (Ft t)
          =ᶠ[nhds (extChartAt I x₀ x₀)]
            fun y : E =>
              (fderiv Real (fun p : Real × E => Φ p.1 p.2) (t, y)) (1, 0)) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet ({x₀} : Set M) F Ft  := by sorry

theorem contDiffAt_prodChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} {F : Real × M -> Real} {t : Real} {x : M}
    (hF : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) n F (t, x)) :
    ContDiffAt Real n
      (fun p : Real × E => F (p.1, (extChartAt I x).symm p.2))
      (t, extChartAt I x x)  := by sorry

theorem fixedBaseOnRegularity_of_timeDerivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {u : Set M}
    {F Ft : Real -> M -> Real}
    (hregular_subset : regularSet ⊆ timeSet)
    (hregular_nhds :
      ∀ {t : Real}, t ∈ regularSet -> timeSet ∈ 𝓝 t)
    (hSmooth :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        ContMDiffAt
          (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
          (fun p : Real × M => F p.1 p.2)
          (t, x))
    (hFdiff :
      ∀ s, s ∈ timeSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x)
    (hFtdiff :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x)
    (hTime :
      ∀ t, t ∈ regularSet -> ∀ x : M,
        HasDerivWithinAt
          (fun s : Real => F s x)
          (Ft t x)
          timeSet
          t) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft  := by sorry

theorem fixedBaseOnRegularityLocal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {timeSet regularSet : Set Real} {u : Set M}
    {F Ft : Real -> M -> Real}
    (hu : IsOpen u)
    (hregular_subset : regularSet ⊆ timeSet)
    (hregular_nhds :
      ∀ {t : Real}, t ∈ regularSet -> timeSet ∈ 𝓝 t)
    (hSmooth :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        ContMDiffAt
          (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
          (fun p : Real × M => F p.1 p.2)
          (t, x))
    (hFdiff :
      ∀ s, s ∈ timeSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (F s) x)
    (hFtdiff :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        MDifferentiableAt I 𝓘(Real, Real) (Ft t) x)
    (hTime :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        HasDerivWithinAt
          (fun s : Real => F s x)
          (Ft t x)
          timeSet
          t) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft  := by sorry

theorem fixedBaseOnRegularitySmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {timeSet regularSet : Set Real} {u : Set M}
    {F Ft : Real -> M -> Real}
    (hu : IsOpen u)
    (hregular_open : IsOpen regularSet)
    (hregular_nhds : ∀ {t : Real}, t ∈ regularSet -> timeSet ∈ nhds t)
    (hSmooth :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        ContMDiffAt
          ((modelWithCornersSelf Real Real).prod I)
          (modelWithCornersSelf Real Real) 2
          (fun p : Real × M => F p.1 p.2)
          (t, x))
    (hTime :
      ∀ t, t ∈ regularSet -> ∀ x : M, x ∈ u ->
        HasDerivWithinAt
          (fun s : Real => F s x)
          (Ft t x)
          timeSet
          t) :
    FixedBaseExtDerivTimeDerivativeOnRegular
      (I := I) timeSet regularSet u F Ft  := by sorry

end DifferentialGeometry

