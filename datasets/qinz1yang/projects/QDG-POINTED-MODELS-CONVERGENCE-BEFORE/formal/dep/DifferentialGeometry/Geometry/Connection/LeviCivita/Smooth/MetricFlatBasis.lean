import dep.DifferentialGeometry.Geometry.Connection.LeviCivita.Characterization.Torsion
import dep.DifferentialGeometry.Geometry.Connection.LeviCivita.Characterization.Uniqueness
import dep.DifferentialGeometry.Geometry.Connection.LocalFrameRegularity
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Smooth
import Mathlib.Geometry.Manifold.VectorBundle.Hom
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section


namespace DifferentialGeometry.Geometry.Connection

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_isLeviCivita_smoothFile
    (g : SmoothRiemannianMetric I M) :
    IsLeviCivita (I := I) (leviCivitaConnectionOfMetric (I := I) g) g  := by sorry

private def localMetricCoeff
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E) (g : SmoothRiemannianMetric I M)
    (i j : ι) (y : M) : Real :=
  g.inner y (e.localFrame b i y) (e.localFrame b j y)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localFrame_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% (e.localFrame b i)) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localMetricCoeff_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localMetricCoeff (I := I) e b g i j y) x  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localMetricCoeff_deriv_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (a i j : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        mvfderiv (I := I)
          (fun q : M => localMetricCoeff (I := I) e b g i j q)
          y (e.localFrame b a y)) x  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem localMetricBracket_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        g.inner y (e.localFrame b i y)
          (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k) y)) x  := by sorry

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_localFrame_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
          (e.localFrame b k) y) x  := by sorry

private noncomputable def coordCLM {ι : Type*} (b : Module.Basis ι Real E) (i : ι) :
    E →L[Real] Real :=
  LinearMap.toContinuousLinearMap (b.coord i)


private noncomputable def basisBilin {ι : Type*} (b : Module.Basis ι Real E) (i j : ι) :
    E →L[Real] E →L[Real] Real :=
  (coordCLM (E := E) b i).smulRight (coordCLM (E := E) b j)

omit [CompleteSpace E] in
private theorem basisBilin_apply {ι : Type*} (b : Module.Basis ι Real E) (i j : ι)
    (v w : E) :
    basisBilin (E := E) b i j v w = b.coord i v * b.coord j w  := by sorry

noncomputable def localMetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (y : M) :
    E →L[Real] E →L[Real] Real :=
  ∑ i : ι, ∑ j : ι,
    localMetricCoeff (I := I) e b g i j y • basisBilin (E := E) b i j

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
private theorem localMetricFlatBasis_apply {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (y : M) (v w : E) :
    localMetricFlatBasis (I := I) e b g y v w =
      ∑ i : ι, ∑ j : ι,
        localMetricCoeff (I := I) e b g i j y * b.coord i v * b.coord j w  := by sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localFrame_sum_coord_smul
    {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet) (v : E) :
    (∑ i : ι, b.coord i v • e.localFrame b i x) = e.symmL Real x v  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
theorem localMetricFlatBasis_eq_inner {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) (v w : E) :
    localMetricFlatBasis (I := I) e b g x v w =
      g.inner x (e.symmL Real x v) (e.symmL Real x w)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
theorem localMetricFlatBasis_isInvertible {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) :
    (localMetricFlatBasis (I := I) e b g x).IsInvertible  := by sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem localMetricFlatBasis_contMDiffAt {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) :
    ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
      (fun y => localMetricFlatBasis (I := I) e b g y) x  := by sorry

private noncomputable def localInvMetricCoeff {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (k l : ι) (y : M) : Real :=
  b.coord k
    ((ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y))
      (coordCLM (E := E) b l))

omit [CompleteSpace E] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem localInvMetricCoeff_contMDiffAt_of_isInvertible {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (hInv : (localMetricFlatBasis (I := I) e b g x).IsInvertible) (k l : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localInvMetricCoeff (I := I) e b g k l y) x  := by sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localInvMetricCoeff_contMDiffAt {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) (k l : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localInvMetricCoeff (I := I) e b g k l y) x  := by sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem coordGInvMdiff
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l
          (extChartAt I x₀ y)) x  := by sorry

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localMetricFlatBasis_eq_dual_sum {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    localMetricFlatBasis (I := I) e b g x v =
      ∑ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) • coordCLM (E := E) b l  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
private theorem basis_coord_eq_sum_localInvMetric_flat {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (k : ι) (v : E) :
    b.coord k v =
      ∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x *
          localMetricFlatBasis (I := I) e b g x v (b l)  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
private theorem localFrame_coeff_eq_sum_localInvMetric_inner {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (k : ι) (V : TangentSpace I x) :
    e.localFrameCoeff I b k x V =
      ∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x *
          g.inner x (e.localFrame b l x) V  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
private theorem lc_christoffel_eq_koszul_sum {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    e.localFrameCoeff I b k x
        ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) x)
          (e.localFrame b i x)) =
      (1 / 2 : Real) *
        ∑ l : ι,
          localInvMetricCoeff (I := I) e b g k l x *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem lc_christoffel_contMDiffAt {ι : Type*} [Finite ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) y)
            (e.localFrame b i y))) x  := by sorry

end DifferentialGeometry.Geometry.Connection

