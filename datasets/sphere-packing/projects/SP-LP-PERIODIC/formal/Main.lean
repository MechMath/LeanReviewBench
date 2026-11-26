module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Basic.IsEmpty.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Order.T5
public import Mathlib.Topology.Separation.CompletelyRegular
public import dep.SpherePacking.Basic.PeriodicPacking
public import dep.SpherePacking.Basic.SpherePacking
public import dep.SpherePacking.CohnElkies.Prereqs

@[expose] public section

open scoped FourierTransform ENNReal SchwartzMap

open SpherePacking Metric BigOperators Pointwise Filter MeasureTheory Complex Real ZSpan
  Bornology Summable Module

variable {d : ℕ}

variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)

variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))

variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))

variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)

variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

local notation "conj" => starRingEnd ℂ

section Complex_Function_Helpers

end Complex_Function_Helpers

section Nonnegativity

end Nonnegativity

section Fundamental_Domain_Dependent

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]

variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)

variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

end Fundamental_Domain_Dependent

section Main_Theorem_For_One_Packing

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]

variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)

variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers

include hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP hD_isBounded hD_unique_covers in
theorem LinearProgrammingBound' (hd : 0 < d) (hf : Summable f) :
  P.density ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
  volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := sorry

end Main_Theorem_For_One_Packing

section Main_Theorem

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

end Main_Theorem
