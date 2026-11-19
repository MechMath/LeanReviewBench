import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section


open Filter
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace AnalyticTransfer

variable {𝕜 X F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma tendsto_slope_of_hasFDerivAt {f : X → F} {f' : X →L[𝕜] F} {x : X}
    (hf : HasFDerivAt f f' x) (v : X) :
    Tendsto (fun t : 𝕜 => t⁻¹ • (f (x + t • v) - f x)) (𝓝[≠] (0 : 𝕜)) (𝓝 (f' v))  := by sorry

lemma mem_submodule_of_hasFDerivAt {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {f : X → F} {f' : X →L[𝕜] F} {x : X} (hf : HasFDerivAt f f' x)
    (hfS : ∀ y, f y ∈ S) (v : X) : f' v ∈ S  := by sorry

lemma hasFDerivAt_codRestrict {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {f : X → F} {f' : X →L[𝕜] F} {x : X} (hf : HasFDerivAt f f' x)
    (hfS : ∀ y, f y ∈ S) :
    HasFDerivAt (fun y => ⟨f y, hfS y⟩ : X → S)
      (f'.codRestrict S (fun v => mem_submodule_of_hasFDerivAt hS hf hfS v)) x  := by sorry

def multilinearValues (S : Submodule 𝕜 F) (k : ℕ) : Submodule 𝕜 (X [×k]→L[𝕜] F) where
  carrier := {T | ∀ v : Fin k → X, T v ∈ S}
  zero_mem' := by intro v; exact S.zero_mem
  add_mem' := by
    intro T U hT hU v
    exact S.add_mem (hT v) (hU v)
  smul_mem' := by
    intro c T hT v
    exact S.smul_mem c (hT v)

lemma isClosed_multilinearValues {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F)) (k : ℕ) :
    IsClosed {T : X [×k]→L[𝕜] F | ∀ v : Fin k → X, T v ∈ S}  := by sorry

lemma fderiv_mem_multilinearValues {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {k : ℕ} {g : X → X [×k]→L[𝕜] F} {g' : X →L[𝕜] X [×k]→L[𝕜] F} {x : X} (hg : HasFDerivAt g g' x)
    (hgS : ∀ y v, g y v ∈ S) (v : X) (w : Fin k → X) : g' v w ∈ S  := by sorry

lemma hasFTaylorSeriesUpTo_coe_mem {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {f : X → F} {p : X → FormalMultilinearSeries 𝕜 X F} {n : WithTop ℕ∞}
    (hp : HasFTaylorSeriesUpTo n f p) (hfS : ∀ x, f x ∈ S) :
    ∀ k : ℕ, k ≤ n → ∀ x : X, ∀ v : Fin k → X, p x k v ∈ S  := by sorry

lemma iteratedFDeriv_mem_submodule {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {f : X → F} {x : X} {n : ℕ} (hf : ContDiff 𝕜 ω f) (hfS : ∀ y, f y ∈ S)
    (v : Fin n → X) : iteratedFDeriv 𝕜 n f x v ∈ S  := by sorry

lemma fpowerSeries_diag_eq_inv_factorial_smul_iteratedFDeriv [CharZero 𝕜]
    {f : X → F} {p : FormalMultilinearSeries 𝕜 X F} {x : X} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x r) (hfa : AnalyticOn 𝕜 f Set.univ) (n : ℕ) (y : X) :
    p n (fun _ : Fin n => y) = ((Nat.factorial n : 𝕜)⁻¹) • iteratedFDeriv 𝕜 n f x
      (fun _ : Fin n => y)  := by sorry

section real

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance mlNormSubmodule (S : Submodule ℝ F) (k : ℕ) :
    Norm (X [×k]→L[ℝ] S) := ⟨fun T =>
      ‖(S.subtypeₗᵢ : S →ₗᵢ[ℝ] F).toContinuousLinearMap.compContinuousMultilinearMap T‖⟩

lemma radius_le_radius_of_norm_le {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂]
    {p : FormalMultilinearSeries ℝ X G₁} {q : FormalMultilinearSeries ℝ X G₂}
    (h : ∀ n, ‖q n‖ ≤ ‖p n‖) : p.radius ≤ q.radius  := by sorry

lemma ftaylorSeries_norm_le {f : X → F} {p : FormalMultilinearSeries ℝ X F} {x : X} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x r) (hfa : AnalyticOn ℝ f Set.univ) (n : ℕ) :
    ‖ftaylorSeries ℝ f x n‖ ≤ (Nat.factorial n : ℝ) * ‖p n‖  := by sorry

lemma analyticOnNhd_codRestrict_real {S : Submodule ℝ F} (hS : IsClosed (S : Set F))
    {f : X → F} (hf : AnalyticOnNhd ℝ f Set.univ) (hfS : ∀ x, f x ∈ S) :
    AnalyticOnNhd ℝ (fun x => ⟨f x, hfS x⟩ : X → S) Set.univ  := by sorry

def linearIsometryEquivRange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E →ₗᵢ[ℝ] F) : E ≃ₗᵢ[ℝ] e.toLinearMap.range where
  toFun := fun x => ⟨e x, LinearMap.mem_range_self (e : E →ₗ[ℝ] F) x⟩
  invFun := fun y => Classical.choose y.2
  left_inv := by
    intro x
    have hspec := Classical.choose_spec
      (show ∃ x' : E, (e : E →ₗ[ℝ] F) x' = e x from
        LinearMap.mem_range_self (e : E →ₗ[ℝ] F) x)
    exact e.injective hspec
  right_inv := by
    intro y
    ext
    exact Classical.choose_spec y.2
  map_add' := by
    intro x y
    ext
    simp [map_add]
  map_smul' := by
    intro c x
    ext
    simp [map_smul]
  norm_map' := by
    intro x
    simp [e.norm_map]

theorem contDiff_of_comp_linearIsometry_omega {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : E →ₗᵢ[ℝ] F) (he : IsClosed (Set.range e)) {g : X → E}
    (hg : ContDiff ℝ ω fun x => e (g x)) : ContDiff ℝ ω g  := by sorry

lemma isClosed_range_comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ψ : E →ₗᵢ[ℝ] F) (hψ : IsClosed (Set.range ψ)) :
    IsClosed (Set.range (fun T : G →L[ℝ] E => ψ.toContinuousLinearMap.comp T))  := by sorry

end real


end AnalyticTransfer

end DifferentialGeometry

end

