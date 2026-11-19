import dep.DifferentialGeometry.Synthetic.Realization.Embedding
import dep.DifferentialGeometry.Synthetic.Realization.Connection
import dep.DifferentialGeometry.Integral.L2.Basic
import dep.DifferentialGeometry.Integral.Measure.Properties
import Mathlib.Topology.Algebra.Support
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator



noncomputable section

open Manifold Set Filter Bundle CovariantDerivative
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]




def compactlySupportedSmoothFunctions
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    Submodule ℝ C^∞⟮I, M; ℝ⟯ where
  carrier := { f : C^∞⟮I, M; ℝ⟯ | HasCompactSupport (f : M → ℝ) }
  zero_mem' := by
    change HasCompactSupport ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    simpa [ContMDiffMap.coe_zero] using
      (HasCompactSupport.zero : HasCompactSupport (0 : M → ℝ))
  add_mem' := by
    intro f f' hf hf'
    change HasCompactSupport ((f + f' : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    simpa [ContMDiffMap.coe_add] using hf.add hf'
  smul_mem' := by
    intro c f hf
    change HasCompactSupport ((c • f : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    
    have h : ((c • f : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (fun _ : M => c) • (f : M → ℝ) := by
      ext x
      simp [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [h]
    exact hf.smul_left

@[simp]
lemma mem_compactlySupportedSmoothFunctions
    {f : C^∞⟮I, M; ℝ⟯} :
    f ∈ compactlySupportedSmoothFunctions I M ↔ HasCompactSupport (f : M → ℝ)  := by sorry

def compactlySupportedSmoothTangentSections
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    Submodule ℝ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  carrier :=
    { X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ |
        HasCompactSupport (fun x : M => (X x : E)) }
  zero_mem' := by
    change HasCompactSupport
      (fun x : M => ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E))
    have h : (fun x : M =>
        ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E)) = (fun _ : M => (0 : E)) := by
      funext x
      change ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E) = (0 : E)
      rfl
    rw [h]
    exact HasCompactSupport.zero
  add_mem' := by
    intro X Y hX hY
    change HasCompactSupport
      (fun x : M =>
        (((X + Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E))
    have h : (fun x : M =>
        (((X + Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E)) =
        (fun x : M => (X x : E)) + (fun x : M => (Y x : E)) := by
      funext x
      change ((X + Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E) =
        ((X x : E) + (Y x : E))
      simp [ContMDiffSection.coe_add, Pi.add_apply]
    rw [h]
    exact hX.add hY
  smul_mem' := by
    intro c X hX
    change HasCompactSupport
      (fun x : M =>
        (((c • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E))
    have h : (fun x : M =>
        (((c • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E)) =
        (fun _ : M => c) • (fun x : M => (X x : E)) := by
      funext x
      change ((c • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E) =
        c • (X x : E)
      simp [ContMDiffSection.coe_smul, Pi.smul_apply]
    rw [h]
    exact hX.smul_left

@[simp]
lemma mem_compactlySupportedSmoothTangentSections
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} :
    X ∈ compactlySupportedSmoothTangentSections I M ↔
      HasCompactSupport (fun x : M => (X x : E))  := by sorry

theorem compactlySupportedSmoothFunctions_mul_mem_left
    {f : C^∞⟮I, M; ℝ⟯} (hf : f ∈ compactlySupportedSmoothFunctions I M)
    (f' : C^∞⟮I, M; ℝ⟯) :
    f * f' ∈ compactlySupportedSmoothFunctions I M  := by sorry

theorem compactlySupportedSmoothFunctions_mul_mem_right
    (f : C^∞⟮I, M; ℝ⟯) {f' : C^∞⟮I, M; ℝ⟯}
    (hf' : f' ∈ compactlySupportedSmoothFunctions I M) :
    f * f' ∈ compactlySupportedSmoothFunctions I M  := by sorry

theorem compactlySupportedSmoothFunctions_mul_mem
    {f f' : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ compactlySupportedSmoothFunctions I M)
    (_hf' : f' ∈ compactlySupportedSmoothFunctions I M) :
    f * f' ∈ compactlySupportedSmoothFunctions I M  := by sorry

section DirectionalDerivative

variable [T2Space M] [SigmaCompactSpace M]


private lemma vectorFieldAction_eq_zero_of_vectorField_eq_zero
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯)
    {x : M} (hx : X x = 0) :
    vectorFieldAction I M X f x = 0  := by sorry

theorem compactlySupportedSmoothTangentSections_action_mem
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hX : X ∈ compactlySupportedSmoothTangentSections I M)
    (f : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X f ∈ compactlySupportedSmoothFunctions I M  := by sorry

theorem compactlySupportedSmoothFunctions_action_of_smooth_section
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ compactlySupportedSmoothFunctions I M) :
    vectorFieldActionSmooth I M X f ∈ compactlySupportedSmoothFunctions I M  := by sorry

end DirectionalDerivative



section CovariantDerivativeClosure

variable [T2Space M] [SigmaCompactSpace M]


theorem compactlySupportedSmoothTangentSections_conn_mem_of_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hX : X ∈ compactlySupportedSmoothTangentSections I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X Y ∈ compactlySupportedSmoothTangentSections I M  := by sorry

theorem compactlySupportedSmoothTangentSections_conn_mem_of_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hY : Y ∈ compactlySupportedSmoothTangentSections I M) :
    concreteConn I M cov X Y ∈ compactlySupportedSmoothTangentSections I M  := by sorry

end CovariantDerivativeClosure



section LpDensity

open MeasureTheory
open scoped ENNReal



private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure


theorem compactlySupportedSmoothFunctions_memLp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    {f : C^∞⟮I, M; ℝ⟯} (hf : f ∈ compactlySupportedSmoothFunctions I M) :
    MeasureTheory.MemLp ((f : M → ℝ)) p
      (riemannianVolumeMeasure (I := I) (M := M) g)  := by sorry

private lemma exists_contMDiff_uniform_approx_sub_compact_support
    [T2Space M] [SigmaCompactSpace M]
    {φ : M → ℝ} (hφ : Continuous φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : C^∞⟮I, M; ℝ⟯,
      (∀ x : M, |(g : M → ℝ) x - φ x| < δ) ∧
        Function.support (g : M → ℝ) ⊆ Function.support φ  := by sorry

private lemma eLpNorm_le_of_bound_and_support_le_measure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    {h : M → ℝ} (_h_meas : AEStronglyMeasurable h
      (riemannianVolumeMeasure (I := I) (M := M) g))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h_bound : ∀ x : M, ‖h x‖ ≤ δ)
    {K : Set M} (hK : IsCompact K)
    (h_supp : ∀ x : M, x ∉ K → h x = 0) :
    eLpNorm h p (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g K) ^ (p.toReal⁻¹) *
        ENNReal.ofReal δ  := by sorry

private lemma exists_smoothCompactSupport_eLpNorm_sub_le_of_continuous
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {φ : M → ℝ} (hφ_cont : Continuous φ) (hφ_supp : HasCompactSupport φ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : C^∞⟮I, M; ℝ⟯,
      f ∈ compactlySupportedSmoothFunctions I M ∧
        eLpNorm (φ - (f : M → ℝ)) p
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ ε  := by sorry

theorem compactlySupportedSmoothFunctions_denseRange_in_Lp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    ∀ (u : MeasureTheory.Lp ℝ p (riemannianVolumeMeasure (I := I) (M := M) g))
      {ε : ℝ} (_hε : 0 < ε),
    ∃ (f : C^∞⟮I, M; ℝ⟯) (hmem : f ∈ compactlySupportedSmoothFunctions I M),
      ‖u - (compactlySupportedSmoothFunctions_memLp (I := I) (M := M) g hmem).toLp
        (f : M → ℝ)‖ < ε  := by sorry

theorem compactlySupportedSmoothFunctions_dense_image_in_Lp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hp' : p ≠ ⊤) :
    Dense (Set.range
      (fun f : compactlySupportedSmoothFunctions I M =>
        ((compactlySupportedSmoothFunctions_memLp (I := I) (M := M) (p := p) g f.2).toLp
          ((f : C^∞⟮I, M; ℝ⟯) : M → ℝ) :
            MeasureTheory.Lp ℝ p (riemannianVolumeMeasure (I := I) (M := M) g))))  := by sorry

end LpDensity

end L2
end Integral
end DifferentialGeometry

end
