import Mathlib

noncomputable section
open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian

abbrev RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

end Riemannian

namespace Riemannian.Tensor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartBasisVecFiber (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    TangentSpace I b :=
  (trivializationAt E (TangentSpace I) α).symm b ((Module.finBasis ℝ E) i)

end Riemannian.Tensor

namespace Riemannian.Tensor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α j x)

end Riemannian.Tensor

namespace Riemannian.Tensor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartInvGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) g α x)⁻¹

end Riemannian.Tensor

namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open Riemannian.Tensor
def partialDeriv (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((Module.finBasis ℝ E) i)

end Riemannian

namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open Riemannian.Tensor
def chartGramOnE (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

end Riemannian

namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open Riemannian.Tensor
def chartChristoffel (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)

end Riemannian

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartCoord (i : Fin (Module.finrank ℝ E)) (v : E) : ℝ :=
  (Module.finBasis ℝ E).repr v i

end Riemannian.Geodesic

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartChristoffelContraction (g : RiemannianMetric I M) (α : M)
    (v w : E) (y : E) : E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j w) •
      Module.finBasis ℝ E k

end Riemannian.Geodesic

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartLocalCurve (γ : ℝ → M) (t : ℝ) : ℝ → E :=
  fun s => extChartAt I (γ t) (γ s)

end Riemannian.Geodesic

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def HasGeodesicEquationAt (g : RiemannianMetric I M) (γ : ℝ → M)
    (t : ℝ) : Prop :=
  ∃ v a : E,
    HasDerivAt (chartLocalCurve (I := I) γ t) v t ∧
    (∀ᶠ s in nhds t, HasDerivAt (chartLocalCurve (I := I) γ t)
        (deriv (chartLocalCurve (I := I) γ t) s) s) ∧
    HasDerivAt (fun s => deriv (chartLocalCurve (I := I) γ t) s) a t ∧
    a + chartChristoffelContraction (I := I) g (γ t) v v
        (extChartAt I (γ t) (γ t)) = 0

end Riemannian.Geodesic

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def IsGeodesicOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasGeodesicEquationAt (I := I) g γ t

end Riemannian.Geodesic

namespace Riemannian.Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def IsGeodesicCurveOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  ContinuousOn γ s ∧ IsGeodesicOn (I := I) g γ s

end Riemannian.Geodesic

namespace MorganTianLib
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev IsGeodesicCurveOn (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  Riemannian.Geodesic.IsGeodesicCurveOn (I := I) g γ s

end MorganTianLib

end
