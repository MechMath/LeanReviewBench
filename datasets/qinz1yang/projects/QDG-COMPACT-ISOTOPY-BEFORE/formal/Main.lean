import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology
section
abbrev loopCircle := UnitAddCircle
end
end DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology
section
abbrev freeLoop (Q : Type*) [TopologicalSpace Q] := C(loopCircle, Q)
end
end DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
section
abbrev Circle := DifferentialGeometry.Topology.loopCircle
end
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
abbrev CurveMap (M : Type*) := AddCircle (1 : ℝ) → ℝ → M
end
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
def lift (c : CurveMap M) (x t : ℝ) : M := c (x : AddCircle (1 : ℝ)) t
end
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
def X (c : CurveMap M) (x t : ℝ) : TangentSpace I (c.lift x t) :=
  mfderiv 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x (1 : ℝ)
end
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
def ImmersedOn (c : CurveMap M) (J : Set ℝ) : Prop :=
  ∀ x t, t ∈ J → c.X (I := I) x t ≠ 0
end
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
def curveOfLoopFamily (γ : ℝ → DifferentialGeometry.Topology.freeLoop M) : CurveMap M := fun z t => γ t z
end
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
open Surgery.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {a b : ℝ}
variable [CompactSpace E] [Nonempty E] [SigmaCompactSpace E]
omit [Nonempty E] in
theorem rfs_csf_boundary_isotopy_modelSpace_of_smoothOn_superwindow {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun p : E × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by sorry
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
