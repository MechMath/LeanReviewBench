module

public import dep.CoarseDeGiorgi.Statements.TriadicCenter
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Multiscale.CubeAverage

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def fivefoldClosedTriadicCube {d : ℕ} (D : TriadicCube d) : Set (Vec d) :=
  {x | ∀ i, |x i - triadicCenter D i| ≤ (5 / 2 : ℝ) * cubeScaleFactor D}

end

end CoarseDeGiorgi
