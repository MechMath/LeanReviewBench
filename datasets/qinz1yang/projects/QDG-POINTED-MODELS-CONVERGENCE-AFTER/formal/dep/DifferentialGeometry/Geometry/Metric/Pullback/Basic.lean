import dep.DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import dep.DifferentialGeometry.Geometry.Metric.Basic
import dep.DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0  := by sorry

noncomputable def Diffeomorph.pullbackInner
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let step1 : TangentSpace I x →L[ℝ] TangentSpace I (Φ x) →L[ℝ] ℝ :=
    (g.inner (Φ x)).comp (mfderiv I I Φ x)
  let precompOp : (TangentSpace I (Φ x) →L[ℝ] ℝ) →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (mfderiv I I Φ x)
  precompOp.comp step1

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem Diffeomorph.pullbackInner_symm
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInner g Φ x v w
      = Diffeomorph.pullbackInner g Φ x w v  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem Diffeomorph.pullbackInner_pos
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < Diffeomorph.pullbackInner g Φ x v v  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem inner_comp_smooth_along_diffeo
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      ((fun b ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g.inner b)) ∘ (Φ : M → N))  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem pullbackInner_eval
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInner g Φ x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w)  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
private theorem mfderiv_eq_mfderivCLE_apply
    (Φ : M ≃ₘ⟮I, I⟯ N) (x : M) (v : TangentSpace I x) :
    Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero x v
      = mfderiv I I Φ x v  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem Diffeomorph.pullbackInner_isVonNBounded
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) :
    ∀ x : M, Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | Diffeomorph.pullbackInner g Φ x v v < 1}  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem mfderiv_apply_section_smooth_along_diffeo
    (Φ : M ≃ₘ⟮I, I⟯ N)
    (Y : ∀ x : M, TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := (TangentSpace I : N → Type _))
        (Φ x) (mfderiv I I (Φ : M → N) x (Y x)))  := by sorry

noncomputable def Diffeomorph.pullbackMetric
    [T2Space M]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SmoothRiemannianMetric I M where
  inner x := Diffeomorph.pullbackInner g Φ x
  symm x v w := Diffeomorph.pullbackInner_symm g Φ x v w
  pos x v hv := Diffeomorph.pullbackInner_pos g Φ x v hv
  isVonNBounded x := Diffeomorph.pullbackInner_isVonNBounded g Φ x
  contMDiff := by
    classical
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (φ := fun x : M => Diffeomorph.pullbackInner g Φ x)
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : M => ℝ)
      (φ := fun x : M => Diffeomorph.pullbackInner g Φ x (Y x))
    intro W
    have hv := mfderiv_apply_section_smooth_along_diffeo Φ (fun x => Y x) Y.contMDiff
    have hw := mfderiv_apply_section_smooth_along_diffeo Φ (fun x => W x) W.contMDiff
    have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x : M => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun b : N => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
          (Φ x) (g.inner (Φ x))) :=
      g.contMDiff.comp Φ.contMDiff
    have h_total : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ
          (E := Bundle.Trivial N ℝ)
          (Φ x)
          (g.inner (Φ x) (mfderiv I I (Φ : M → N) x (Y x))
            (mfderiv I I (Φ : M → N) x (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun b : N => TangentSpace I b)
        (E₂ := fun b : N => TangentSpace I b)
        (E₃ := fun _ : N => ℝ)
        (b := fun x : M => Φ x)
        (ψ := fun x : M => g.inner (Φ x))
        (v := fun x : M => mfderiv I I (Φ : M → N) x (Y x))
        (w := fun x : M => mfderiv I I (Φ : M → N) x (W x))
        hg hv hw
    have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => g.inner (Φ x) (mfderiv I I (Φ : M → N) x (Y x))
            (mfderiv I I (Φ : M → N) x (W x))) := by
      intro x
      have h_at := h_total x
      rw [contMDiffAt_totalSpace] at h_at
      simpa using h_at.2
    have h_pullback_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Diffeomorph.pullbackInner g Φ x (Y x) (W x)) := by
      have h_eq : (fun x : M => Diffeomorph.pullbackInner g Φ x (Y x) (W x))
          = fun x : M => g.inner (Φ x) (mfderiv I I (Φ : M → N) x (Y x))
              (mfderiv I I (Φ : M → N) x (W x)) := by
        funext x; exact pullbackInner_eval g Φ x (Y x) (W x)
      rw [h_eq]; exact h_scalar
    intro x
    rw [contMDiffAt_section]
    refine (h_pullback_smooth.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards with y
    change Diffeomorph.pullbackInner g Φ y (Y y) (W y) =
      (trivializationAt ℝ (Bundle.Trivial M ℝ) x
        ⟨y, Diffeomorph.pullbackInner g Φ y (Y y) (W y)⟩).2
    rfl


theorem Diffeomorph.pullbackMetric_inner
    [T2Space M]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (x : M) (v w : TangentSpace I x) :
    (Diffeomorph.pullbackMetric g Φ).inner x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w)  := by sorry

theorem Diffeomorph.pullbackMetric_refl
    [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    Diffeomorph.pullbackMetric g (_root_.Diffeomorph.refl I M ∞) = g  := by sorry

theorem Diffeomorph.pullbackMetric_trans
    {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I P) (Φ : M ≃ₘ⟮I, I⟯ N) (Ψ : N ≃ₘ⟮I, I⟯ P) :
    Diffeomorph.pullbackMetric (Diffeomorph.pullbackMetric g Ψ) Φ =
      Diffeomorph.pullbackMetric g (Φ.trans Ψ)  := by sorry

theorem Diffeomorph.pullbackInner_contMDiff
    [T2Space M]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        ((Diffeomorph.pullbackInner g Φ x : E →L[ℝ] E →L[ℝ] ℝ)))  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem Diffeomorph.mfderiv_contMDiff
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    ContMDiff I I ∞ (Φ : M → N)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem bilinear_comp_self_contMDiff :
    ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
        ContinuousLinearMap.bilinearComp p.1 p.2 p.2)  := by sorry

end DifferentialGeometry

