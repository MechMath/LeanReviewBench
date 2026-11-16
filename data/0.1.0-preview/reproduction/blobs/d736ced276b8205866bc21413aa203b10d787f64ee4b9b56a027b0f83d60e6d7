module

public import dep.CoarseDeGiorgi.Statements.ClosedTriadicCube
public import dep.CoarseDeGiorgi.Statements.WhitneyAdmissible
public import dep.Homogenization.Multiscale.CubeAverage

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def whitneyCubes {d : ℕ} (τ : ℝ) : Set (TriadicCube d) :=
  {D | whitneyAdmissible τ D ∧
    ∀ E, whitneyAdmissible τ E → closedTriadicCube D ⊆ closedTriadicCube E → E = D}

end

end CoarseDeGiorgi
