import Mathlib
import dep.Common

noncomputable section

open Set Function MeasureTheory

open scoped ContDiff

structure equivariant_map where
  to_fun : ℝ → ℝ
  eqv' : ∀ t, to_fun (t + 1) = to_fun t + 1

instance : CoeFun equivariant_map (fun _ => ℝ → ℝ) := ⟨equivariant_map.to_fun⟩

structure circle_diffeo extends equivariant_map where
  smooth' : ∀ t, smooth_at to_fun t
  deriv' : ∀ t, deriv to_fun t ≠ 0

instance : CoeFun circle_diffeo (fun _ => ℝ → ℝ) := ⟨fun f => f.to_fun⟩

instance : Coe circle_diffeo equivariant_map := ⟨fun f => ⟨f.to_fun, f.eqv'⟩⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

def loop.reparam (γ : loop F) (φ : equivariant_map) : loop F where
  to_fun := γ ∘ φ
  per' t := sorry

lemma reparametrization {g b : E → F} {U : Set E}
  (γ : E → ℝ → loop F) (h_surr : surrounding_family g b γ U)
  (h_smooth : ∀ x ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s,
    smooth_at (fun p : E × ℝ × ℝ => γ p.1 p.2.1 p.2.2) (x, t, s)) :
  ∃ φ : E → circle_diffeo, ∀ x ∈ U,
    (∀ s, smooth_at (fun p : E × ℝ => φ p.1 p.2) (x, s)) ∧
    φ x 0 = 0 ∧ ((γ x 1).reparam (φ x)).average = g x := sorry
