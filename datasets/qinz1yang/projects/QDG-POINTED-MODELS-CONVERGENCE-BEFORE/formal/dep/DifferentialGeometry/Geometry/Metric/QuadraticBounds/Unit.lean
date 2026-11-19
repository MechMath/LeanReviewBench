import dep.DifferentialGeometry.Tensor.RSTensor.PositiveSemidefinite
import dep.DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import dep.DifferentialGeometry.Geometry.Metric.Basic
import dep.DifferentialGeometry.Tensor.RSTensor.Defs
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import dep.DifferentialGeometry.Tensor.Alternating.Composition
import dep.DifferentialGeometry.Tensor.Multilinear.Composition
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import dep.DifferentialGeometry.Tensor.Multilinear.Smoothness.LinearIsometry
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import dep.DifferentialGeometry.Tensor.Multilinear.Curry.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import dep.DifferentialGeometry.Tensor.RSTensor.Field
import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation

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

def MetricUnitTangent (g : SmoothRiemannianMetric I M) : Type _ :=
  {p : TangentBundle I M // g.inner p.proj p.2 p.2 = 1}

instance metricUnitTop (g : SmoothRiemannianMetric I M) :
    TopologicalSpace (MetricUnitTangent (I := I) (M := M) g) :=
  inferInstanceAs (TopologicalSpace
    {p : TangentBundle I M // g.inner p.proj p.2 p.2 = 1})

namespace MetricUnitTangent

def base {g : SmoothRiemannianMetric I M}
    (p : MetricUnitTangent (I := I) (M := M) g) : M :=
  (p.1).proj

def vec {g : SmoothRiemannianMetric I M}
    (p : MetricUnitTangent (I := I) (M := M) g) :
    TangentSpace I (base (I := I) (M := M) p) :=
  (p.1).2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem unit {g : SmoothRiemannianMetric I M}
    (p : MetricUnitTangent (I := I) (M := M) g) :
    g.inner (base (I := I) (M := M) p)
      (vec (I := I) (M := M) p) (vec (I := I) (M := M) p) = 1  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem base_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    base (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        MetricUnitTangent (I := I) (M := M) g) = x  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem vec_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    vec (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        MetricUnitTangent (I := I) (M := M) g) = v  := by sorry

end MetricUnitTangent

def MetricUnitTangentSlab
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real) : Type _ :=
  Σ t : {t : Real // t ∈ Set.Icc t0 t1}, MetricUnitTangent (I := I) (M := M) (G t.1)

instance metricUnitTangentSlabTop
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real) :
    TopologicalSpace (MetricUnitTangentSlab (I := I) (M := M) G t0 t1) :=
  inferInstanceAs (TopologicalSpace
    (Σ t : {t : Real // t ∈ Set.Icc t0 t1},
      MetricUnitTangent (I := I) (M := M) (G t.1)))

def MetricUnitTangentTimeSlab
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real) : Type _ :=
  {q : ({t : Real // t ∈ K} × TangentBundle I M) //
    (G q.1.1).inner q.2.proj q.2.2 q.2.2 = 1}

instance metricUnitTangentTimeSlabTop
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real) :
    TopologicalSpace (MetricUnitTangentTimeSlab (I := I) (M := M) G K) :=
  inferInstanceAs (TopologicalSpace
    {q : ({t : Real // t ∈ K} × TangentBundle I M) //
      (G q.1.1).inner q.2.proj q.2.2 q.2.2 = 1})

abbrev MetricUnitTangentIccSlab
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real) : Type _ :=
  MetricUnitTangentTimeSlab (I := I) (M := M) G (Set.Icc t0 t1)

namespace MetricUnitTangentTimeSlab

def time {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) : Real :=
  q.1.1.1

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem time_mem {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    time (I := I) (M := M) q ∈ K  := by sorry

def bundlePoint {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    TangentBundle I M :=
  q.1.2

def base {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) : M :=
  (bundlePoint (I := I) (M := M) q).proj

def vec {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    TangentSpace I (base (I := I) (M := M) q) :=
  (bundlePoint (I := I) (M := M) q).2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem unit {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    (G (time (I := I) (M := M) q)).inner
      (base (I := I) (M := M) q)
      (vec (I := I) (M := M) q) (vec (I := I) (M := M) q) = 1  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem time_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    time (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) = t  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem bundlePoint_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    bundlePoint (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) =
      (⟨x, v⟩ : TangentBundle I M)  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem base_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    base (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) = x  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem vec_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    vec (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) = v  := by sorry

end MetricUnitTangentTimeSlab

omit [FiniteDimensional ℝ E] in
theorem metricQuad_cont
    (g : SmoothRiemannianMetric I M) :
    Continuous (fun p : TangentBundle I M => g.inner p.proj p.2 p.2)  := by sorry

omit [FiniteDimensional ℝ E] in
theorem metricUnit_closed
    (g : SmoothRiemannianMetric I M) :
    IsClosed {p : TangentBundle I M | g.inner p.proj p.2 p.2 = 1}  := by sorry

private theorem coordMetric_lower
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M}
    (hK : IsCompact K)
    (hKsub : K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ c : Real, 0 < c ∧
      ∀ x ∈ K, ∀ w : E, ‖w‖ = 1 →
        c ≤ g.inner x
          ((trivializationAt E (TangentSpace I) x₀).symmL Real x w)
          ((trivializationAt E (TangentSpace I) x₀).symmL Real x w)  := by sorry

private theorem coordMetric_bound
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M}
    (hK : IsCompact K)
    (hKsub : K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ R : Real, 0 ≤ R ∧
      ∀ y ∈ K, ∀ v : TangentSpace I y,
        g.inner y v v = 1 →
          ‖(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt Real y v‖ ≤ R  := by sorry

private theorem unitRest_compact
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E
        (TangentSpace I : M → Type _) → M))
    [e.IsLinear Real]
    {K : Set M} (hK : IsCompact K) (hKe : K ⊆ e.baseSet)
    {R : Real} (_hR : 0 ≤ R)
    (hbound : ∀ y ∈ K, ∀ v : TangentSpace I y,
      g.inner y v v = 1 →
        ‖e.continuousLinearMapAt Real y v‖ ≤ R) :
    IsCompact {p : MetricUnitTangent (I := I) (M := M) g |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K}  := by sorry

theorem metricUnitOn_compact
    [T2Space M]
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) :
    IsCompact {p : MetricUnitTangent (I := I) (M := M) g |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K}  := by sorry

theorem metricUnit_compact
    [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    IsCompact (Set.univ : Set (MetricUnitTangent (I := I) (M := M) g))  := by sorry

theorem metricUnit_quadCont
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) 2) :
    Continuous (fun p : MetricUnitTangent (I := I) (M := M) g =>
      quad02 (I := I) (M := M)
        (A (MetricUnitTangent.base (I := I) (M := M) p))
        (MetricUnitTangent.vec (I := I) (M := M) p))  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem metric_smul2
    (g : SmoothRiemannianMetric I M) {x : M}
    (a : Real) (v : TangentSpace I x) :
    g.inner x (a • v) (a • v) = a * a * g.inner x v v  := by sorry

end DifferentialGeometry

