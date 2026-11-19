import dep.DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import dep.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

def metricTimeBundleQuad
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  (G q.1.1).inner q.2.proj q.2.2 q.2.2

def metricUnitTimeSlabRefQuad
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    Real :=
  (G q.1.1).inner
    (MetricUnitTangent.base (I := I) (M := M) q.2)
    (MetricUnitTangent.vec (I := I) (M := M) q.2)
    (MetricUnitTangent.vec (I := I) (M := M) q.2)

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabRefQuad_cont_of_bundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad : Continuous (metricTimeBundleQuad (I := I) (M := M) G K)) :
    Continuous (metricUnitTimeSlabRefQuad (I := I) (M := M) G K g₀)  := by sorry

noncomputable def metricUnitTimeSlabScale
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    Real :=
  (Real.sqrt (metricUnitTimeSlabRefQuad (I := I) (M := M) G K g₀ q))⁻¹

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem metricUnitTimeSlabRefQuad_pos
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    0 < metricUnitTimeSlabRefQuad (I := I) (M := M) G K g₀ q  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabScale_cont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad :
      Continuous (metricUnitTimeSlabRefQuad (I := I) (M := M) G K g₀)) :
    Continuous (metricUnitTimeSlabScale (I := I) (M := M) G K g₀)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabScale_cont_of_bundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad : Continuous (metricTimeBundleQuad (I := I) (M := M) G K)) :
    Continuous (metricUnitTimeSlabScale (I := I) (M := M) G K g₀)  := by sorry

noncomputable def metricUnitTimeSlabScaledBundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    TangentBundle I M :=
  ⟨MetricUnitTangent.base (I := I) (M := M) q.2,
    metricUnitTimeSlabScale (I := I) (M := M) G K g₀ q •
      MetricUnitTangent.vec (I := I) (M := M) q.2⟩

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem metricUnitTimeSlabScaledBundle_unit
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    (G q.1.1).inner
      (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q).proj
      (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q).2
      (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀ q).2 = 1  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem tangentBundle_smul_cont :
    Continuous (fun p : Real × TangentBundle I M =>
      (⟨p.2.proj, p.1 • p.2.2⟩ : TangentBundle I M))  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabScaledBundle_cont_of_bundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad : Continuous (metricTimeBundleQuad (I := I) (M := M) G K)) :
    Continuous (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀)  := by sorry

noncomputable def metricUnitTimeSlabParam
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    MetricUnitTangentTimeSlab (I := I) (M := M) G K := by
  let t : Real := q.1.1
  let x : M := MetricUnitTangent.base (I := I) (M := M) q.2
  let v : TangentSpace I x := MetricUnitTangent.vec (I := I) (M := M) q.2
  have hv : v ≠ 0 := by
    intro hv0
    have hbad : (0 : Real) = 1 := by
      simpa [x, v, hv0] using
        (MetricUnitTangent.unit (I := I) (M := M) q.2)
    norm_num at hbad
  let r : Real := (G t).inner x v v
  have hrpos : 0 < r := (G t).pos x v hv
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let u : TangentSpace I x := a • v
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have hunit : (G t).inner x u u = 1 := by
    have haa : a * a * r = 1 := by
      have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
        field_simp [hsne]
      calc
        a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
          rw [hss]
        _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
        _ = 1 := hmul
    calc
      (G t).inner x u u = a * a * r := by
        simpa [u, r] using metric_smul2 (I := I) (M := M) (G t) a v
      _ = 1 := haa
  exact ⟨(q.1, (⟨x, u⟩ : TangentBundle I M)), hunit⟩

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem metricUnitTimeSlabParam_time
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (q : {t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀) :
    MetricUnitTangentTimeSlab.time (I := I) (M := M)
      (metricUnitTimeSlabParam (I := I) (M := M) G K g₀ q) = q.1.1  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabParam_cont_of_scaledBundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hscaled :
      Continuous (metricUnitTimeSlabScaledBundle (I := I) (M := M) G K g₀)) :
    Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlabParam_cont_of_bundle
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad : Continuous (metricTimeBundleQuad (I := I) (M := M) G K)) :
    Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀)  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem metricUnitTimeSlabParam_surjective
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M) :
    Function.Surjective
      (metricUnitTimeSlabParam (I := I) (M := M) G K g₀)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlab_compact_of_param
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hsource :
      IsCompact
        (Set.univ :
          Set ({t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀)))
    (hcont :
      Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀))
    (hsurj :
      Function.Surjective
        (metricUnitTimeSlabParam (I := I) (M := M) G K g₀)) :
    IsCompact
      (Set.univ : Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K))  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlab_compact_of_param_cont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hsource :
      IsCompact
        (Set.univ :
          Set ({t : Real // t ∈ K} × MetricUnitTangent (I := I) (M := M) g₀)))
    (hcont :
      Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀)) :
    IsCompact
      (Set.univ : Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K))  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricUnitTimeSlab_compact_of_param_cont_compactSpace
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (g₀ : SmoothRiemannianMetric I M)
    [CompactSpace {t : Real // t ∈ K}]
    [CompactSpace (MetricUnitTangent (I := I) (M := M) g₀)]
    (hcont :
      Continuous (metricUnitTimeSlabParam (I := I) (M := M) G K g₀)) :
    IsCompact
      (Set.univ : Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K))  := by sorry

theorem metricUnitTimeSlab_icc_compact_of_param_cont
    [CompactSpace M] [T2Space M]
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hcont :
      Continuous (metricUnitTimeSlabParam (I := I) (M := M)
        G (Set.Icc t0 t1) g₀)) :
    IsCompact
      (Set.univ :
        Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
          (Set.Icc t0 t1)))  := by sorry

theorem metricUnitTimeSlab_icc_compact_of_bundle
    [CompactSpace M] [T2Space M]
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real)
    (g₀ : SmoothRiemannianMetric I M)
    (hquad :
      Continuous (metricTimeBundleQuad (I := I) (M := M) G (Set.Icc t0 t1))) :
    IsCompact
      (Set.univ :
        Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
          (Set.Icc t0 t1)))  := by sorry

omit [FiniteDimensional ℝ E] in
theorem unitAbsBound_to_all
    (g : SmoothRiemannianMetric I M)
    (A : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {C : Real}
    (hunit :
      ∀ p : MetricUnitTangent (I := I) (M := M) g,
        |quad02 (I := I) (M := M)
          (A (MetricUnitTangent.base (I := I) (M := M) p))
          (MetricUnitTangent.vec (I := I) (M := M) p)| ≤ C) :
    ∀ x (v : TangentSpace I x),
      |quad02 (I := I) (M := M) (A x) v| ≤ C * g.inner x v v  := by sorry

omit [FiniteDimensional ℝ E] in
theorem compactUnitSlab_absBound
    (G : Real -> SmoothRiemannianMetric I M)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (t0 t1 : Real)
    [TopologicalSpace (MetricUnitTangentSlab (I := I) (M := M) G t0 t1)]
    (hcompact :
      IsCompact (Set.univ : Set (MetricUnitTangentSlab (I := I) (M := M) G t0 t1)))
    (hcont : Continuous
      (fun p : MetricUnitTangentSlab (I := I) (M := M) G t0 t1 =>
        |quad02 (I := I) (M := M)
          (A p.1.1 (MetricUnitTangent.base (I := I) (M := M) p.2))
          (MetricUnitTangent.vec (I := I) (M := M) p.2)|)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ Set.Icc t0 t1 ->
        ∀ x (v : TangentSpace I x),
          |quad02 (I := I) (M := M) (A t x) v| ≤ C * (G t).inner x v v  := by sorry

omit [FiniteDimensional ℝ E] in
theorem compactUnitTimeSlab_absBound
    (G : Real -> SmoothRiemannianMetric I M)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (K : Set Real)
    (hcompact :
      IsCompact
        (Set.univ :
          Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K)))
    (hcont : Continuous
      (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        |quad02 (I := I) (M := M)
          (A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
            (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
          (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ K ->
        ∀ x (v : TangentSpace I x),
          |quad02 (I := I) (M := M) (A t x) v| ≤ C * (G t).inner x v v  := by sorry

theorem timeSlabAbsQuadCont
    (G : Real -> SmoothRiemannianMetric I M)
    (A : (t : Real) -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (K : Set Real)
    (hA :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (A q.1.1 q.2.proj))) :
    Continuous
      (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        |quad02 (I := I) (M := M)
          (A (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
            (MetricUnitTangentTimeSlab.base (I := I) (M := M) p))
          (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)|)  := by sorry

theorem metric_lower_icc
    [CompactSpace M] [T2Space M]
    (G : Real → SmoothRiemannianMetric I M) (t0 t1 : Real)
    (gRef : SmoothRiemannianMetric I M)
    (hquad :
      Continuous
        (metricTimeBundleQuad (I := I) (M := M) G (Set.Icc t0 t1))) :
    ∃ c : Real, 0 < c ∧
      ∀ t, t ∈ Set.Icc t0 t1 →
        ∀ x (v : TangentSpace I x),
          c * gRef.inner x v v ≤ (G t).inner x v v  := by sorry

end DifferentialGeometry

