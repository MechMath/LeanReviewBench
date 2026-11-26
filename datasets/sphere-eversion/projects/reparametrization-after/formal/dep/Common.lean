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
