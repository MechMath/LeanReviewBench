module

public import Mathlib.MeasureTheory.MeasurableSpace.Instances

public section

/-- `BitVec n` is finite, hence countable.

Mathlib derives `Fintype (BitVec n)` from `FinEnum (BitVec n)` (`Mathlib.Data.FinEnum`), which this
module deliberately does not import; the `Finite` instance is restated here so that this module
stands alone: without `Countable` in scope,
`MeasurableSingletonClass.toDiscreteMeasurableSpace` does not fire, and the discrete structure
below fails to propagate to products and function types — which is exactly what cryptographic
sampling statements are built from. `Finite` is `Prop`-valued, so this cannot conflict with any
`Fintype` instance. -/
instance BitVec.instFinite (n : ℕ) : Finite (BitVec n) := sorry

instance BitVec.instMeasurableSpace (n : ℕ) : MeasurableSpace (BitVec n) := ⊤

instance BitVec.instMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (BitVec n) := sorry

instance BitVec.instDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (BitVec n) := sorry
