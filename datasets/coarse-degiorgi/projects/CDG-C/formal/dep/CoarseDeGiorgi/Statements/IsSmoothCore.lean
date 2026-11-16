module

public import dep.CoarseDeGiorgi.Statements.SmoothGrad
public import dep.CoarseDeGiorgi.Statements.WeightedEnergy
public import dep.Homogenization.Ambient.CoefficientField
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def IsSmoothCore {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) φ V ∧
    IntegrableOn φ V ∧
    weightedEnergy a V (smoothGrad φ) < ⊤

end CoarseDeGiorgi
