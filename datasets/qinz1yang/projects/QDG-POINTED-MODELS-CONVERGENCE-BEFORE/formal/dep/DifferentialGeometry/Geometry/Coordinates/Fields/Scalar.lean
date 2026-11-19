import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def scalarOnE (x₀ : M) (f : M → ℝ) : E → ℝ :=
  fun y => f ((extChartAt I x₀).symm y)

omit [IsManifold I ∞ M] in
@[simp] lemma scalarOnE_def (x₀ : M) (f : M → ℝ) (y : E) :
    scalarOnE (I := I) x₀ f y = f ((extChartAt I x₀).symm y)  := by sorry

omit [IsManifold I ∞ M] in
lemma scalarOnE_extChartAt (x₀ : M) (f : M → ℝ) {x : M}
    (hx : x ∈ (extChartAt I x₀).source) :
    scalarOnE (I := I) x₀ f (extChartAt I x₀ x) = f x  := by sorry

lemma scalarOnE_contDiffOn (x₀ : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (scalarOnE (I := I) x₀ f)
      (extChartAt I x₀).target  := by sorry

lemma scalarOnE_contDiffOn_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (x₀ : M) {f : P → M → ℝ} {s : Set P}
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => f p.1 p.2) (s ×ˢ univ)) :
    ContDiffOn ℝ ∞
      (fun p : P × E => scalarOnE (I := I) x₀ (f p.1) p.2)
      (s ×ˢ (extChartAt I x₀).target)  := by sorry

lemma scalarOnE_contDiffWithinAt
    (x₀ : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffWithinAt ℝ ∞ (scalarOnE (I := I) x₀ f)
      (extChartAt I x₀).target y  := by sorry

end DifferentialGeometry.Tensor.Coordinates

