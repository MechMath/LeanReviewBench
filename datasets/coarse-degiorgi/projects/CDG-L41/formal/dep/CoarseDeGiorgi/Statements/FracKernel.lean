module

public import dep.CoarseDeGiorgi.Statements.FracKernelWithDimension
public import dep.Homogenization.Ambient.CoefficientField

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def fracKernel {d : ℕ} (α r : ℝ) (w : Vec d → ℝ)
    (p : Vec d × Vec d) : ℝ≥0∞ :=
  fracKernelWithDimension (d : ℝ) α r w p

end

end CoarseDeGiorgi
