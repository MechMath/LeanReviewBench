import dep.DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartCoeff (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun x => (chartModelBasis E).repr
    ((trivializationAt E (TangentSpace I) x₀) ⟨x, X x⟩).2 i

@[simp] lemma chartCoeff_def (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    chartCoeff (I := I) x₀ X i x =
      (chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) x₀) ⟨x, X x⟩).2 i  := by sorry

lemma chartCoeff_recompose (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    X x = ∑ i, chartCoeff (I := I) x₀ X i x •
      chartBasisVecFiber (I := I) x₀ i x  := by sorry

lemma chartCoeff_contMDiffOn (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartCoeff (I := I) x₀ X i)
      (trivializationAt E (TangentSpace I) x₀).baseSet  := by sorry

def chartCoeffOnE (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartCoeff (I := I) x₀ X i ((extChartAt I x₀).symm y)

lemma chartCoeffOnE_contDiffOn (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x₀ X i)
      (extChartAt I x₀).target  := by sorry

end DifferentialGeometry.Tensor.Coordinates

