import Mathlib
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff Topology
structure loop (X : Type*) where
  to_fun : ℝ → X
  per' : ∀ t, to_fun (t + 1) = to_fun t
instance {X : Type*} : CoeFun (loop X) (fun _ => ℝ → X) := ⟨loop.to_fun⟩
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
def smooth_at (f : E → F) (x : E) : Prop :=
  ∃ s ∈ 𝓝 x, ContDiffOn ℝ ∞ f s
lemma smooth_at.continuous_at {f : E → F} {x : E} (h : smooth_at f x) : ContinuousAt f x := by
  obtain ⟨s, hs, h⟩ := h
  exact h.continuousOn.continuousAt hs
structure surrounding_pts (f : F) (p : Fin (Module.finrank ℝ F + 1) → F)
    (w : Fin (Module.finrank ℝ F + 1) → ℝ) : Prop where
  indep : AffineIndependent ℝ p
  w_pos : ∀ i, 0 < w i
  w_sum : ∑ i, w i = 1
  avg : ∑ i, w i • p i = f
namespace loop
def surrounds (γ : loop F) (x : F) : Prop :=
  ∃ t w : Fin (Module.finrank ℝ F + 1) → ℝ, surrounding_pts x (γ ∘ t) w
noncomputable def average [MeasurableSpace F] [BorelSpace F] (γ : loop F) : F :=
  ∫ t in (0 : ℝ)..1, γ t
end loop
structure surrounding_family (g b : E → F) (γ : E → ℝ → loop F) (U : Set E) : Prop where
  base : ∀ (x : E) (t : ℝ), γ x t 0 = b x
  t₀ : ∀ (x : E) (s : ℝ), γ x 0 s = b x
  surrounds : ∀ x ∈ U, (γ x 1).surrounds (g x)
  cont : Continuous (fun p : E × ℝ × ℝ => γ p.1 p.2.1 p.2.2)
