import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.ODE.Gronwall

noncomputable section
open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff Matrix BigOperators
namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
namespace DifferentialGeometry.Integral.DivergenceTheorem
end DifferentialGeometry.Integral.DivergenceTheorem
namespace DifferentialGeometry.Geometry.Riemannian.Geodesic
end DifferentialGeometry.Geometry.Riemannian.Geodesic
namespace DifferentialGeometry.Geometry.Riemannian.AlongCurve
end DifferentialGeometry.Geometry.Riemannian.AlongCurve
namespace DifferentialGeometry.Integral.Measure
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
abbrev SmoothRiemannianMetric (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)
end
end DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Integral.Measure
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
@[irreducible] def chartModelBasis (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map
    (toEuclidean (E := E)).symm.toLinearEquiv
end
end DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Integral.Measure
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
def chartBasisVecFiber (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symm x ((chartModelBasis E) i)
end
end DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Integral.Measure
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
def chartGramMatrix (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) x₀ i x)
      (chartBasisVecFiber (I := I) x₀ j x)
end
end DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Integral.DivergenceTheorem
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def chartInvGramMatrix (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) g α x)⁻¹
end
end DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry.Integral.DivergenceTheorem
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def partialDeriv (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((chartModelBasis E) i)
end
end DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry.Integral.DivergenceTheorem
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def chartGramOnE (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j
end
end DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry.Integral.DivergenceTheorem
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def chartChristoffel (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)
end
end DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def chartCoord (i : Fin (Module.finrank ℝ E)) (v : E) : ℝ :=
  (chartModelBasis E).repr v i
end
end DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def chartChristoffelContraction (g : SmoothRiemannianMetric I M) (α : M)
    (v w : E) (y : E) : E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j w) •
      chartModelBasis E k
end
end DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.AlongCurve
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
@[ext] structure SectionAlongCurve (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (_γ : ℝ → M) where
  
  toFun : ℝ → E
end
end DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.Geometry.Riemannian.AlongCurve
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def chartCurve (α : M) (γ : ℝ → M) : ℝ → E :=
  fun t => extChartAt I α (γ t)
end
end DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.Geometry.Riemannian.AlongCurve
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def IsCovDerivAlongChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y W : ℝ → E) (s : Set ℝ) : Prop :=
  (∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) ∧
    ∀ t ∈ s, HasDerivAt Y
      (W t - chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t
end
end DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.Geometry.Riemannian.AlongCurve
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def IsParallelChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y : ℝ → E) (s : Set ℝ) : Prop :=
  IsCovDerivAlongChart (I := I) g α γ uPrime Y (fun _ => (0 : E)) s
end
end DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.Geometry.Riemannian.AlongCurve
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
def chartGramAlongCurve (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (V W : ℝ → E) (t : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
      chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)
end
end DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.Geometry.Riemannian.Variation
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
theorem parallel_global_extension
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ : E) :
    ∃! V : ℝ → E,
      V t₀ = v₀ ∧
      (∀ α : M, ∀ s : Set ℝ, (∀ t ∈ s, γ t ∈ (chartAt H α).source) →
        IsParallelChart (I := I) g α γ
          (fun t => deriv (chartCurve (I := I) α γ) t) V s) := by sorry
end
end DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.Variation
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
noncomputable def parallelTransport
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ : E) : SectionAlongCurve I M γ :=
  ⟨(parallel_global_extension (I := I) g γ hγ t₀ v₀).exists.choose⟩
end
end DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.Variation
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Riemannian.AlongCurve
theorem parallelTransport_preserves_inner_product
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (t₀ : ℝ) (v₀ w₀ : E) (t : ℝ) :
    g.inner (γ t)
        ((parallelTransport (I := I) g γ hγ t₀ v₀).toFun t)
        ((parallelTransport (I := I) g γ hγ t₀ w₀).toFun t) =
      g.inner (γ t₀) v₀ w₀ := by sorry
end
end DifferentialGeometry.Geometry.Riemannian.Variation

