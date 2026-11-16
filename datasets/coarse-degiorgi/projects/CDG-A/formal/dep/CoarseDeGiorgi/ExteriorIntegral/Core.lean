module

public import dep.CoarseDeGiorgi.ExteriorIntegral.Geometry
public import dep.CoarseDeGiorgi.ExteriorIntegral.Algebra
public import dep.CoarseDeGiorgi.ExteriorIntegral.Holder
public import dep.CoarseDeGiorgi.Harnack.Pairing.ArbitraryLayer
public import dep.CoarseDeGiorgi.Harnack.WeakHarnack.SelectionAdapters
public import dep.CoarseDeGiorgi.Selection.SourceRepresentatives
public import dep.CoarseDeGiorgi.Weighted.GradientHilbert
public import dep.CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
public import dep.CoarseDeGiorgi.Statements.SelectionInterval
public import dep.CoarseDeGiorgi.Statements.MemH1a
public import dep.CoarseDeGiorgi.Whitney.LiftZeroExtension
public import dep.CoarseDeGiorgi.Statements.SampledUpperResponse
public import dep.CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension

/-! # The layer-by-layer bound for the exterior integral -/

@[expose] public section

namespace CoarseDeGiorgi.ExteriorIntegral

open Homogenization MeasureTheory Set Whitney
open scoped ENNReal

noncomputable section

instance instCountableExteriorCell {d : ℕ} {τ : ℝ} : Countable (ExteriorCell d τ) := by
  unfold ExteriorCell
  infer_instance

theorem isClosed_closedReferenceCube {d : ℕ} (τ : ℝ) :
    IsClosed (closedReferenceCube (d := d) τ) := by
  have : closedReferenceCube (d := d) τ = ⋂ i, {x : Vec d | |x i| ≤ τ / 2} := by
    ext x
    simp [closedReferenceCube]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

end

end CoarseDeGiorgi.ExteriorIntegral
