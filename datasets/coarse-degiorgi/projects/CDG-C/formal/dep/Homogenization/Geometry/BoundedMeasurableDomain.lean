module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Bounded
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Geometry.Domain

@[expose] public section

namespace Homogenization

open scoped ENNReal

/-- A bounded measurable subset of `R^d` with strictly positive Lebesgue volume. -/
structure BoundedMeasurableDomain (d : ℕ) where
  /-- The underlying measurable subset of `R^d`. -/
  carrier : Set (Vec d)
  measurableSet : MeasurableSet carrier
  isBoundedDomain : IsBoundedDomain carrier
  volume_pos : 0 < MeasureTheory.volume carrier

namespace BoundedMeasurableDomain

instance {d : ℕ} : SetLike (BoundedMeasurableDomain d) (Vec d) where
  coe U := U.carrier
  coe_injective := sorry

/-- Restricted Lebesgue measure on a bounded measurable domain. -/
noncomputable def restrictedVolume {d : ℕ} (U : BoundedMeasurableDomain d) :
    MeasureTheory.Measure (Vec d) :=
  MeasureTheory.volume.restrict U

/-- The probability measure obtained by normalizing restricted Lebesgue measure. -/
noncomputable def normalizedVolume {d : ℕ} (U : BoundedMeasurableDomain d) :
    MeasureTheory.Measure (Vec d) :=
  (MeasureTheory.volume (U : Set (Vec d)))⁻¹ • U.restrictedVolume

end BoundedMeasurableDomain

end Homogenization
