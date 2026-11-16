module

public import dep.CoarseDeGiorgi.Statements.SurfaceMeasure
public import dep.CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import dep.CoarseDeGiorgi.Statements.OriginCube

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def surfaceEnergyMaximal {d : ℕ} (ρ R : ℝ) (a : CoeffField d)
    (_ha : IsWeightedCoeffOn (originCube 1) a) (G : Vec d → Vec d) (τ : ℝ) : ℝ≥0∞ :=
  ⨆ ε : ℝ, ⨆ (_hε : 0 < ε),
    (ENNReal.ofReal (2 * ε))⁻¹ *
      ∫⁻ l in Set.Ioo (τ - ε) (τ + ε) ∩ Set.Ioo ρ R,
        ∫⁻ x, ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))
          ∂(surfaceMeasure l)

end CoarseDeGiorgi
