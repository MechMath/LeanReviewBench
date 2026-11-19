import Mathlib
import dep.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Basic
import dep.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import dep.DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section
open Bundle Manifold Set Finset Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal Matrix Bundle
universe u uE uH
namespace DifferentialGeometry.Geometry.Operator
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator


def chartChristoffel (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)
end
end DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Geometry.Curvature
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator


def chartRiemannTensor (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y +
    (∑ m : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g α j m l y *
          chartChristoffel (I := I) g α i k m y -
        chartChristoffel (I := I) g α k m l y *
          chartChristoffel (I := I) g α i j m y))
end
end DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.Geometry.Riemannian
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature


def chartRiemannLower (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g α l m y *
      chartRiemannTensor (I := I) g α i j k m y
end
end DifferentialGeometry.Geometry.Riemannian
namespace DifferentialGeometry.Geometry.Riemannian
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature


def sectionalCurvatureNumerator (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) l *
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) i *
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) j *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w) k *
                  chartRiemannLower (I := I) g p i j k l (extChartAt I p p)
end
end DifferentialGeometry.Geometry.Riemannian
namespace DifferentialGeometry.Geometry.Riemannian
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature


def sectionalCurvatureDenominator (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2
end
end DifferentialGeometry.Geometry.Riemannian
namespace DifferentialGeometry.Geometry.Riemannian
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature


def sectionalCurvature (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  sectionalCurvatureNumerator (I := I) g p v w /
    sectionalCurvatureDenominator (I := I) g p v w
end
end DifferentialGeometry.Geometry.Riemannian
namespace DifferentialGeometry.Geometry.Hyperbolic
section
variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry


def hasConstantSectionalCurvature (g : SmoothRiemannianMetric (𝓡 3) M) (K : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace (𝓡 3) p),
    LinearIndependent ℝ ![v, w] → Geometry.Riemannian.sectionalCurvature g p v w = K
end
end DifferentialGeometry.Geometry.Hyperbolic
noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
def chartDensity (g : SmoothRiemannianMetric I M) (x₀ : M) : M → ℝ :=
  fun x => Real.sqrt (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g x₀ x).det
noncomputable def modelHaar : MeasureTheory.Measure E := (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).addHaar
def chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.map (extChartAt I x₀).symm
    (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
      (fun y : E =>
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y))))
variable (I M) in
def chartAtlasPOU [T2Space M] [SigmaCompactSpace M] :
    SmoothPartitionOfUnity M I M univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose
def riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.sum fun α : M =>
    (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))
variable (I M) in
def riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) : MeasureTheory.Measure M :=
  riemannianMeasure (I := I) g (chartAtlasPOU I M)
end DifferentialGeometry.Integral.Measure
end
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Bundle
namespace DifferentialGeometry.CheegerGromovCompactness
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
structure PointedRiemannianManifold
    (I : ModelWithCorners Real E H) where
  M : Type u
  [topology : TopologicalSpace M]
  [charted : ChartedSpace H M]
  [smooth : IsManifold I ∞ M]
  [sigmaCompact : SigmaCompactSpace M]
  [t2 : T2Space M]
  [t2TangentBundle : T2Space (TangentBundle I M)]
  basepoint : M
  metric : SmoothRiemannianMetric I M
structure PointedRiemannianSeq (I : ModelWithCorners Real E H) where
  obj : Nat -> PointedRiemannianManifold.{u, uE, uH} (I := I)
end DifferentialGeometry.CheegerGromovCompactness
namespace DifferentialGeometry
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
def tangentChartEquiv (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    TangentSpace I x ≃ₗ[ℝ] E :=
  (trivializationAt E (TangentSpace I) p).linearEquivAt ℝ x hx
structure ManifoldOrientation (n : ℕ) [FiniteDimensional ℝ E] where
  dimension_eq : Module.finrank ℝ E = n
  orientation : (x : M) → Orientation ℝ (TangentSpace I x) (Fin n)
  locally_constant : ∀ p x : M,
    ∀ hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet,
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (trivializationAt E (TangentSpace I) p).baseSet,
      ∀ y : M, ∀ hy : y ∈ U,
        Orientation.map (Fin n) (tangentChartEquiv I M p y (hU hy)) (orientation y) =
          Orientation.map (Fin n) (tangentChartEquiv I M p x hx) (orientation x)
end
end DifferentialGeometry
namespace DifferentialGeometry
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace in
structure RiemannianMetricComplete
    (g : SmoothRiemannianMetric I M) : Prop where
  complete :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M
end
end DifferentialGeometry


open Bundle Manifold Set
open scoped Manifold Topology ContDiff
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness
section

structure ExhaustsByOpen {M : Type*} [TopologicalSpace M]
    (U : Nat -> Set M) : Prop where
  isOpen : forall k : Nat, IsOpen (U k)
  mono_step : forall k : Nat, U k ⊆ U (k + 1)
  subset :
    forall K : Set M, IsCompact K ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ U k
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
structure PointedRiemannianConvergenceMaps
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat) where
  partialDiffeomorph :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      PartialDiffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞)
  source_exhausts :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    ExhaustsByOpen (fun k =>
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      (partialDiffeomorph k).source)
  base_mem :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      L.basepoint ∈ (partialDiffeomorph k).source
  basepoint_map :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
def source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) : Set L.M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).source
end
end DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps

namespace DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
def target
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    Set ((X.obj (subseq k)).M) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).target
end
end DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps

namespace DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
def map
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    L.M -> (X.obj (subseq k)).M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact fun x => (Φ.partialDiffeomorph k) x
end
end DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps

namespace DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem source_open
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsOpen (Φ.source k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps

namespace DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem target_open
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    IsOpen (Φ.target k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps

namespace DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
omit [CompleteSpace E] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem isSigmaCompact_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsSigmaCompact (Phi.source k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps

namespace DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
omit [CompleteSpace E] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem isSigmaCompact_target
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    IsSigmaCompact (Phi.target k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
def metricSourceOpenSubset
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    TopologicalSpace.Opens L.M := by
  letI : TopologicalSpace L.M := L.topology
  exact ⟨Φ.source k, Φ.source_open k⟩
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
def metricTargetOpenSubset
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).topology
    TopologicalSpace.Opens ((X.obj (subseq k)).M) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  exact ⟨Φ.target k, Φ.target_open k⟩
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
abbrev MetricSourceDomain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :=
  letI : TopologicalSpace L.M := L.topology
  (metricSourceOpenSubset (I := I) Φ k : Type _)
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
abbrev MetricTargetDomain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :=
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  (metricTargetOpenSubset (I := I) Φ k : Type _)
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
@[implicit_reducible]
noncomputable def metricSourceDomainTopology
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    TopologicalSpace (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  change TopologicalSpace (metricSourceOpenSubset (I := I) Φ k)
  infer_instance
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
@[implicit_reducible]
noncomputable def metricSourceDomainChartedSpace
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    ChartedSpace H (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  change ChartedSpace H (metricSourceOpenSubset (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H) (M := L.M)
    (s := metricSourceOpenSubset (I := I) Φ k)
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem metric_source_domain_smooth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainChartedSpace (I := I) Φ k
    IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
@[implicit_reducible]
noncomputable def metricTargetDomainTopology
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    TopologicalSpace (MetricTargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  change TopologicalSpace (metricTargetOpenSubset (I := I) Φ k)
  infer_instance
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
@[implicit_reducible]
noncomputable def metricTargetDomainChartedSpace
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    ChartedSpace H (MetricTargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  change ChartedSpace H (metricTargetOpenSubset (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H)
    (M := (X.obj (subseq k)).M) (s := metricTargetOpenSubset (I := I) Φ k)
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem metric_target_domain_smooth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
noncomputable def metricSourceTargetDiffeomorph
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainChartedSpace (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    Diffeomorph I I (MetricSourceDomain (I := I) Φ k)
      (MetricTargetDomain (I := I) Φ k) (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : IsManifold I ∞ L.M := L.smooth
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : IsManifold I ∞ (X.obj (subseq k)).M :=
    (X.obj (subseq k)).smooth
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainChartedSpace (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metric_source_domain_smooth (I := I) Φ k
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainChartedSpace (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_smooth (I := I) Φ k
  let e := Φ.partialDiffeomorph k
  refine
    { toEquiv := e.toPartialEquiv.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · sorry
  · sorry
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
def metricSourceCompactSet
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    (K : Set L.M) : Set (MetricSourceDomain (I := I) Φ k) :=
  {x | (x : L.M) ∈ K}
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem metric_source_domain_t2
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    T2Space (MetricSourceDomain (I := I) Φ k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem metric_target_domain_t2
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    T2Space (MetricTargetDomain (I := I) Φ k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metric_source_domain_sigma_compact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    (hσ : letI : TopologicalSpace L.M := L.topology; IsSigmaCompact (Φ.source k)) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metric_target_domain_sigma_compact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    (hσ :
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      IsSigmaCompact (Φ.target k)) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) := by sorry
end
end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)
abbrev ThreeModel := 𝓘(ℝ, ThreeSpace)
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace DifferentialGeometry.Geometry.Hyperbolic
structure FiniteVolumeHyperbolicModel where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Carrier]
  [smooth : IsManifold (𝓡 3) ∞ Carrier]
  [hausdorff : T2Space Carrier]
  [sigmaCompact : SigmaCompactSpace Carrier]
  [connected : ConnectedSpace Carrier]
  orientation : ManifoldOrientation (𝓡 3) Carrier 3
  metric : SmoothRiemannianMetric (𝓡 3) Carrier
  basepoint : Carrier
  curvature : hasConstantSectionalCurvature metric (-(1 / 4 : ℝ))
  complete : RiemannianMetricComplete metric
  finite_volume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) Carrier metric univ < ⊤
attribute [instance] FiniteVolumeHyperbolicModel.topology FiniteVolumeHyperbolicModel.charts FiniteVolumeHyperbolicModel.smooth FiniteVolumeHyperbolicModel.hausdorff FiniteVolumeHyperbolicModel.sigmaCompact FiniteVolumeHyperbolicModel.connected
end DifferentialGeometry.Geometry.Hyperbolic
namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M]
noncomputable def metricDiffCovDerivAt
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (a + 2) x :=
  metricCovDeriv (I := I) gk gRef a x -
    metricCovDeriv (I := I) gInf gRef a x
noncomputable def metricDerivNorm
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (metricDiffCovDerivAt (I := I) a gk gInf gRef x))
noncomputable def metricDerivNormSupOn
    (K : Set M) (p : Nat)
    (gk gInf gRef : SmoothRiemannianMetric I M) : Real :=
  sSup {r : Real |
    exists a : Nat, a <= p ∧
      exists x : M, x ∈ K ∧
        metricDerivNorm (I := I) a gk gInf gRef x = r}
end
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
structure MetricSourceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) where
  topology : TopologicalSpace (MetricSourceDomain (I := I) Φ k)
  charted : ChartedSpace H (MetricSourceDomain (I := I) Φ k)
  t2 : T2Space (MetricSourceDomain (I := I) Φ k)
  smooth : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k)
  sigmaCompact : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k)
  limitMetric :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)
  pullbackMetric :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)
  referenceMetric :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)
  compact_preimage :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : TopologicalSpace L.M := L.topology
    forall K : Set L.M, IsCompact K ->
      K ⊆ Φ.source k ->
      IsCompact (metricSourceCompactSet (I := I) Φ k K)
  limit_inner :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
      limitMetric.inner x v w =
        L.metric.inner (x : L.M)
          ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v)
          ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w)
  pullback_inner :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : TopologicalSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M :=
      (X.obj (subseq k)).charted
    letI : T2Space (X.obj (subseq k)).M :=
      (X.obj (subseq k)).t2
    letI : IsManifold I ∞ (X.obj (subseq k)).M :=
      (X.obj (subseq k)).smooth
    letI : SigmaCompactSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).sigmaCompact
    forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
      pullbackMetric.inner x v w =
        (X.obj (subseq k)).metric.inner
          (Φ.map k (x : L.M))
          ((mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
          ((mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)
namespace MetricSourceData
noncomputable def derivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {k : Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) : Real := by
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  letI : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (MetricSourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (MetricSourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  exact metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Φ k K) p
    D.pullbackMetric D.limitMetric D.referenceMetric
end MetricSourceData
def metricSourceConvergesOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (D : forall k : Nat, MetricSourceData (I := I) Φ k)
    (K : Set L.M)
    (p : Nat) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\ (D k).derivNormSupOn (I := I) K p < ε
structure MetricConvergenceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) where
  domain : forall k : Nat, MetricSourceData (I := I) Φ k
  converges :
    forall K : Set L.M,
      (letI : TopologicalSpace L.M := L.topology; IsCompact K) →
      forall p : Nat, metricSourceConvergesOn (I := I) Φ domain K p
end
end DifferentialGeometry.CheegerGromovCompactness
namespace DifferentialGeometry.CheegerGromovCompactness
section
variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metric_source_compact_set_is_compact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    {K : Set L.M}
    (hK :
      letI : TopologicalSpace L.M := L.topology
      IsCompact K)
    (hKsrc :
      letI : TopologicalSpace L.M := L.topology
      K ⊆ Φ.source k) :
    letI : TopologicalSpace L.M := L.topology
    IsCompact (metricSourceCompactSet (I := I) Φ k K)  := by sorry
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp]
theorem metric_source_target_diffeomorph_apply
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat)
    (x : MetricSourceDomain (I := I) Φ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomainChartedSpace (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainTopology (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomainChartedSpace (I := I) Φ k
    (metricSourceTargetDiffeomorph (I := I) Φ k x : (X.obj (subseq k)).M) =
      Φ.map k (x : L.M)  := by sorry
namespace MetricSourceData
noncomputable def ofCanonical
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    {k : Nat}
    (sigmaCompact :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      SigmaCompactSpace (MetricSourceDomain (I := I) Φ k))
    (limitMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (pullbackMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (referenceMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (limit_inner :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
        limitMetric.inner x v w =
          L.metric.inner (x : L.M)
            ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v)
            ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w))
    (pullback_inner :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      letI : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
      letI : IsManifold I ∞ (X.obj (subseq k)).M :=
        (X.obj (subseq k)).smooth
      letI : SigmaCompactSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).sigmaCompact
      forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
        pullbackMetric.inner x v w =
          (X.obj (subseq k)).metric.inner
            (Φ.map k (x : L.M))
            ((mfderiv I I
              (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
            ((mfderiv I I
              (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)) :
    MetricSourceData (I := I) Φ k where
  topology := metricSourceDomainTopology (I := I) Φ k
  charted := metricSourceDomainChartedSpace (I := I) Φ k
  t2 := metric_source_domain_t2 (I := I) Φ k
  smooth := metric_source_domain_smooth (I := I) Φ k
  sigmaCompact := sigmaCompact
  limitMetric := limitMetric
  pullbackMetric := pullbackMetric
  referenceMetric := referenceMetric
  compact_preimage := by
    intro K hK hKsrc
    exact metric_source_compact_set_is_compact (I := I) Φ k hK hKsrc
  limit_inner := limit_inner
  pullback_inner := pullback_inner
noncomputable def ofRestrictPullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    {k : Nat}
    (hσsource : letI : TopologicalSpace L.M := L.topology; IsSigmaCompact (Φ.source k))
    (referenceMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)) :
    MetricSourceData (I := I) Φ k := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
    change IsManifold I ∞ L.M
    infer_instance
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  letI : IsManifold I ∞ (X.obj (subseq k)).M :=
    (X.obj (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (subseq k)).M := by
    change IsManifold I ∞ (X.obj (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).sigmaCompact
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainTopology (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomainChartedSpace (I := I) Φ k
  letI : T2Space (MetricSourceDomain (I := I) Φ k) := metric_source_domain_t2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metric_source_domain_smooth (I := I) Φ k
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
    metric_source_domain_sigma_compact (I := I) Φ k hσsource
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainTopology (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomainChartedSpace (I := I) Φ k
  letI : T2Space (MetricTargetDomain (I := I) Φ k) := metric_target_domain_t2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metric_target_domain_smooth (I := I) Φ k
  refine MetricSourceData.ofCanonical (I := I)
    (Φ := Φ) (k := k)
    (metric_source_domain_sigma_compact (I := I) Φ k hσsource)
    (by
      let sourceT2 : T2Space (metricSourceOpenSubset (I := I) Φ k) := by
        change T2Space (MetricSourceDomain (I := I) Φ k)
        exact metric_source_domain_t2 (I := I) Φ k
      exact
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          L.M L.topology L.charted L.smooth inferInstance
          L.metric (metricSourceOpenSubset (I := I) Φ k) sourceT2)
    (by
      let sourceT2 : T2Space (metricSourceOpenSubset (I := I) Φ k) := by
        change T2Space (MetricSourceDomain (I := I) Φ k)
        exact metric_source_domain_t2 (I := I) Φ k
      let targetT2 : T2Space (metricTargetOpenSubset (I := I) Φ k) := by
        change T2Space (MetricTargetDomain (I := I) Φ k)
        exact metric_target_domain_t2 (I := I) Φ k
      let targetMetric : SmoothRiemannianMetric I (metricTargetOpenSubset (I := I) Φ k) :=
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          (X.obj (subseq k)).M (X.obj (subseq k)).topology
          (X.obj (subseq k)).charted (X.obj (subseq k)).smooth inferInstance
          (X.obj (subseq k)).metric (metricTargetOpenSubset (I := I) Φ k)
          targetT2
      exact
        @Diffeomorph.pullbackMetric E inferInstance inferInstance inferInstance H inferInstance I
          (MetricSourceDomain (I := I) Φ k) (metricSourceDomainTopology (I := I) Φ k)
          (metricSourceDomainChartedSpace (I := I) Φ k) (metric_source_domain_smooth (I := I) Φ k)
          (MetricTargetDomain (I := I) Φ k) (metricTargetDomainTopology (I := I) Φ k)
          (metricTargetDomainChartedSpace (I := I) Φ k) (metric_target_domain_smooth (I := I) Φ k)
          sourceT2 targetMetric (metricSourceTargetDiffeomorph (I := I) Φ k))
    referenceMetric
    ?_ ?_
  all_goals sorry
end MetricSourceData
end
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
namespace CanonicalMetricCompactness
noncomputable def canonicalReferenceMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomainTopology (I := I) Phi k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomainChartedSpace (I := I) Phi k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
      metric_source_domain_smooth (I := I) Phi k
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Phi k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainTopology (I := I) Phi k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainChartedSpace (I := I) Phi k
  letI : T2Space (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_t2 (I := I) Phi k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_smooth (I := I) Phi k
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_sigma_compact (I := I) Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source (I := I) Phi k)
  exact L.metric.restrictOpen (I := I) (metricSourceOpenSubset (I := I) Phi k)
noncomputable def canonicalSourceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq) (k : Nat) :
    MetricSourceData (I := I) Phi k :=
  MetricSourceData.ofRestrictPullback (I := I)
    (Φ := Phi) (k := k) (PointedRiemannianConvergenceMaps.isSigmaCompact_source (I := I) Phi k)
    (canonicalReferenceMetric (I := I) Phi k)
end CanonicalMetricCompactness
end
end DifferentialGeometry.CheegerGromovCompactness
namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
def modelPointed_S13 (M : FiniteVolumeHyperbolicModel.{u}) :
    PointedRiemannianManifold.{u, 0, 0} (I := ThreeModel) where
  M := M.Carrier
  topology := inferInstance
  charted := inferInstance
  smooth := inferInstance
  sigmaCompact := inferInstance
  t2 := inferInstance
  t2TangentBundle := inferInstance
  basepoint := M.basepoint
  metric := M.metric
local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
def PointedModelsConverge_S13 (models : ℕ → FiniteVolumeHyperbolicModel.{u})
    (M : FiniteVolumeHyperbolicModel.{u}) : Prop :=
  ∃ Φ : PointedRiemannianConvergenceMaps
      (⟨fun j => modelPointed_S13 (models j)⟩ : PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel))
      (modelPointed_S13 M) id,
    ∃ C : MetricConvergenceData Φ,
      ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k
end GC.LongTime.Ch12
