import dep.DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis

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
theorem leviCivitaConnectionOfMetric_homSection_contMDiffAt
    {ι : Type*} [Finite ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun y : M =>
        (⟨y, leviCivitaConnectionOfMetric (I := I) g σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_homSection_contMDiffAt_one
    {ι : Type*} [Finite ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) (1 : WithTop ℕ∞)
      (fun y : M =>
        (⟨y, leviCivitaConnectionOfMetric (I := I) g σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M)
      (leviCivitaConnectionOfMetric (I := I) g) ∞  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g) ∞  := by sorry

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M)
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞)  := by sorry

end DifferentialGeometry.Geometry.Connection

