import Mathlib

open Real

noncomputable def riemannZeta.zeroes : Set ℂ := {s : ℂ | riemannZeta s = 0}

noncomputable def riemannZeta.zeroes_rect (I J : Set ℝ) : Set ℂ :=
  {s : ℂ | s.re ∈ I ∧ s.im ∈ J ∧ s ∈ zeroes}

noncomputable def riemannZeta.order (s : ℂ) : ℤ := (meromorphicOrderAt (riemannZeta) s).untopD 0

noncomputable def riemannZeta.zeroes_sum {α : Type*} [RCLike α]
    (I J : Set ℝ) (f : ℂ → α) : α :=
  ∑' ρ : riemannZeta.zeroes_rect I J, (f ρ) * (riemannZeta.order ρ)

noncomputable def riemannZeta.N' (σ T : ℝ) : ℝ := zeroes_sum (Set.Ioo σ 1) (Set.Ioo 0 T) 1

structure zero_density_bound where
  T₀ : ℝ
  σ_range : Set ℝ
  c₁ : ℝ → ℝ
  c₂ : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  bound : ∀ T ≥ T₀, ∀ σ ∈ σ_range,
      riemannZeta.N' σ T ≤ (c₁ σ) * T ^ (p σ) * (log T) ^ (q σ) + (c₂ σ) * (log T) ^ 2
