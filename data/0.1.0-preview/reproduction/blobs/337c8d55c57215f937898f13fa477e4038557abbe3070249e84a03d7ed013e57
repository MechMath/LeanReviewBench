module

public import dep.CoarseDeGiorgi.Statements.OriginCube

public import dep.CoarseDeGiorgi.NegSobolev.SobolevNormFacts

@[expose] public section

open Homogenization MeasureTheory

namespace CoarseDeGiorgi

/-- The cubes `ρ □₀` are open ("Cubes and simplices are open"). -/
theorem isOpen_originCube {d : ℕ} (ρ : ℝ) : IsOpen (originCube (d := d) ρ)
:=
  by exact CoarseDeGiorgi.NegSobolev.isOpen_originCube ρ

end CoarseDeGiorgi
