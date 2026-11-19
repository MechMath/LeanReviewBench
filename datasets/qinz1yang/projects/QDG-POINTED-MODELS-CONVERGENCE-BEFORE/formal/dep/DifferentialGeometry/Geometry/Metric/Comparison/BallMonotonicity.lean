import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import dep.DifferentialGeometry.Geometry.Metric.Basic

set_option autoImplicit false

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

theorem ball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.ball x r ⊆ Metric.ball x R  := by sorry

theorem cball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.closedBall x r ⊆ Metric.closedBall x R  := by sorry

theorem injOn_of_return
    {X Y ι : Type*} [PseudoMetricSpace X]
    {S : Set X} {F : X → Y} {H : Y → X}
    (K V : ι → Set X) {ρ : Real}
    (hρ : 0 < ρ)
    (hcover : S ⊆ ⋃ i, K i)
    (hbuffer : ∀ i x, x ∈ K i → Metric.ball x ρ ⊆ V i)
    (hlocal : ∀ i, Set.InjOn F (V i))
    (hreturn : ∀ x, x ∈ S → dist (H (F x)) x < ρ / 2) :
    Set.InjOn F S  := by sorry

end DifferentialGeometry

