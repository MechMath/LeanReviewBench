module

public import dep.CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import dep.CoarseDeGiorgi.Statements.SurfaceMeasure
public import dep.Homogenization.Ambient.CoefficientField
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def surfaceFracNorm {d : ℕ} (τ α r : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ((ENNReal.rpow (eLpNorm f (ENNReal.ofReal r) (surfaceMeasure τ)) r) +
    ENNReal.rpow (surfaceFracSeminorm τ α r f) r).rpow (1 / r)

end

end CoarseDeGiorgi
