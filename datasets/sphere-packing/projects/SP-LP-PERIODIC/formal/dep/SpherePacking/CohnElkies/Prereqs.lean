module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
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

@[expose] public section

open BigOperators Bornology

variable {d : ℕ} [Fact (0 < d)]

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section Euclidean_Space

instance instNonemptyFin : Nonempty (Fin d) := sorry

end Euclidean_Space

open scoped FourierTransform

open Complex Real

open LinearMap (BilinForm)

noncomputable section PSF_L

def PSF_Conditions (f : EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  /-
    Mention here all the conditions we decide to impose functions on which to define the PSF-L.
    For example, this could be that they must be Schwartz (cf. blueprint) or admissible (cf. Cohn-
    Elkies). This is a placeholder for now, as is almost everything in this file.

    I think Schwartz is a good choice, because we can use the results in
    `Mathlib.Analysis.Distribution.FourierSchwartz` to conclude various things about the function.
  -/
  Summable f ∧
  sorry

theorem PSF_L {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f)
  (v : EuclideanSpace ℝ (Fin d)) :
  ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
    ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ _) Λ,
  (𝓕 f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) := sorry

namespace SchwartzMap

end SchwartzMap

end PSF_L

open scoped FourierTransform

section Positivity_on_Nhd

variable {E : Type*} [TopologicalSpace E]

open MeasureTheory

variable [MeasureSpace E] [BorelSpace E]

end Positivity_on_Nhd

section Integration

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E]

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]

variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)]

instance : (volume : Measure E).IsOpenPosMeasure := sorry

namespace SchwartzMap

end SchwartzMap

end Integration

noncomputable section Misc

instance (v : EuclideanSpace ℝ (Fin d)) : Decidable (v = 0) := Classical.propDecidable (v = 0)

instance : DecidableEq (EuclideanSpace ℝ (Fin d)) :=
  Classical.typeDecidableEq (EuclideanSpace ℝ (Fin d))

omit [Fact (0 < d)]

local notation "conj" => starRingEnd ℂ

end Misc
