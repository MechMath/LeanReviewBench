import dep.DifferentialGeometry.Geometry.Metric.Basic
import dep.DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import dep.DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry


open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def SmoothRiemannianMetric.restrictOpenInner
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) (x : U) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
  g.inner (x : M)

@[simp]
theorem SmoothRiemannianMetric.restrictOpenInner_apply
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v w : TangentSpace I x) :
    g.restrictOpenInner (I := I) U x v w = g.inner (x : M) v w  := by sorry

theorem SmoothRiemannianMetric.restrictOpenInner_symm
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v w : TangentSpace I x) :
    g.restrictOpenInner (I := I) U x v w =
      g.restrictOpenInner (I := I) U x w v  := by sorry

theorem SmoothRiemannianMetric.restrictOpenInner_pos
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < g.restrictOpenInner (I := I) U x v v  := by sorry

theorem SmoothRiemannianMetric.restrictOpenInner_isVonNBounded
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) :
    ∀ x : U, Bornology.IsVonNBounded Real
      {v : TangentSpace I x | g.restrictOpenInner (I := I) U x v v < 1}  := by sorry

variable [FiniteDimensional Real E]

theorem SmoothRiemannianMetric.restrictOpenInner_contMDiff
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] :
    letI : TopologicalSpace U := inferInstance
    letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := M) (s := U)
    letI : IsManifold I ∞ U :=
      { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun x : U => TotalSpace.mk' (E →L[Real] E →L[Real] Real) x
        (g.restrictOpenInner (I := I) U x))  := by sorry

noncomputable def SmoothRiemannianMetric.restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] :
    letI : TopologicalSpace U := inferInstance
    letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := M) (s := U)
    letI : IsManifold I ∞ U :=
      { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    SmoothRiemannianMetric I U where
  inner x := g.restrictOpenInner (I := I) U x
  symm x v w := g.restrictOpenInner_symm (I := I) U x v w
  pos x v hv := g.restrictOpenInner_pos (I := I) U x v hv
  isVonNBounded := g.restrictOpenInner_isVonNBounded (I := I) U
  contMDiff := g.restrictOpenInner_contMDiff (I := I) U

@[simp]
theorem SmoothRiemannianMetric.restrictOpen_inner
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U]
    (x : U) (v w : TangentSpace I x) :
    letI : TopologicalSpace U := inferInstance
    letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := M) (s := U)
    letI : IsManifold I ∞ U :=
      { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    (g.restrictOpen (I := I) U).inner x v w = g.inner (x : M) v w  := by sorry

noncomputable def SmoothRiemannianMetric.restrictOpenOfSubset
    {U V : TopologicalSpace.Opens M} (g : SmoothRiemannianMetric I U) (hVU : V ≤ U)
    [T2Space V] : SmoothRiemannianMetric I V where
  inner x := g.inner (TopologicalSpace.Opens.inclusion hVU x)
  symm x v w := g.symm (TopologicalSpace.Opens.inclusion hVU x) v w
  pos x v hv := g.pos (TopologicalSpace.Opens.inclusion hVU x) v hv
  isVonNBounded x := by
    exact g.isVonNBounded (TopologicalSpace.Opens.inclusion hVU x)
  contMDiff := by
    let incl : V → U := TopologicalSpace.Opens.inclusion hVU
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun x : V => TangentSpace I x →L[Real] Real)
      (φ := fun x : V => g.inner (incl x))
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : V => Real)
      (φ := fun x : V => g.inner (incl x) (Y x))
    intro W
    have hinclTan : ContMDiff I.tangent I.tangent ∞ (tangentMap I I incl) :=
      (contMDiff_inclusion hVU).contMDiff_tangentMap (le_refl _)
    have hY :
        ContMDiff I (I.prod 𝓘(Real, E)) ∞
          (fun x : V => TotalSpace.mk' E (incl x) ((mfderiv I I incl x) (Y x))) := by
      change ContMDiff I I.tangent ∞ (tangentMap I I incl ∘ fun x => ⟨x, Y x⟩)
      exact hinclTan.comp Y.contMDiff
    have hW :
        ContMDiff I (I.prod 𝓘(Real, E)) ∞
          (fun x : V => TotalSpace.mk' E (incl x) ((mfderiv I I incl x) (W x))) := by
      change ContMDiff I I.tangent ∞ (tangentMap I I incl ∘ fun x => ⟨x, W x⟩)
      exact hinclTan.comp W.contMDiff
    have hg :
        ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
          (fun x : V => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun b : U => TangentSpace I b →L[Real] TangentSpace I b →L[Real] Real)
            (incl x) (g.inner (incl x))) := by
      exact g.contMDiff.comp (contMDiff_inclusion hVU)
    have htotal :
        ContMDiff I (I.prod 𝓘(Real, Real)) ∞
          (fun x : V => TotalSpace.mk' Real
            (E := Bundle.Trivial U Real) (incl x)
            (g.inner (incl x) ((mfderiv I I incl x) (Y x))
              ((mfderiv I I incl x) (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun b : U => TangentSpace I b)
        (E₂ := fun b : U => TangentSpace I b)
        (E₃ := fun _ : U => Real)
        (b := incl) (ψ := fun x : V => g.inner (incl x))
        (v := fun x : V => (mfderiv I I incl x) (Y x))
        (w := fun x : V => (mfderiv I I incl x) (W x)) hg hY hW
    have hscalar : ContMDiff I 𝓘(Real, Real) ∞
        (fun x : V => g.inner (incl x) (Y x) (W x)) := by
      have hscalar' : ContMDiff I 𝓘(Real, Real) ∞
          (fun x : V => g.inner (incl x) ((mfderiv I I incl x) (Y x))
            ((mfderiv I I incl x) (W x))) := by
        intro x
        have hat := htotal x
        rw [contMDiffAt_totalSpace] at hat
        simpa using hat.2
      have hYeq : ∀ x : V, (mfderiv I I incl x) (Y x) = Y x := by
        intro x
        rw [mfderiv_opens_incl]
        rfl
      have hWeq : ∀ x : V, (mfderiv I I incl x) (W x) = W x := by
        intro x
        rw [mfderiv_opens_incl]
        rfl
      simpa only [hYeq, hWeq] using hscalar'
    intro x
    rw [contMDiffAt_section]
    refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl


@[simp] theorem SmoothRiemannianMetric.restrictSubset_inner
    {U V : TopologicalSpace.Opens M} (g : SmoothRiemannianMetric I U) (hVU : V ≤ U)
    [T2Space V] (x : V) (v w : TangentSpace I x) :
    (g.restrictOpenOfSubset (I := I) hVU).inner x v w =
      g.inner (TopologicalSpace.Opens.inclusion hVU x) v w  := by sorry

omit [FiniteDimensional Real E] in
private theorem metric_eq_inner
    {g g' : SmoothRiemannianMetric I M}
    (h : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) :
    g = g'  := by sorry

@[simp] theorem SmoothRiemannianMetric.restrictOpen_flat
    (g : SmoothRiemannianMetric I M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    [T2Space U] [T2Space V] :
    (g.restrictOpen (I := I) U).restrictOpenOfSubset (I := I) hVU =
      g.restrictOpen (I := I) V  := by sorry

end DifferentialGeometry

