module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.Ergodic.Action.Regular
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
public import dep.SpherePacking.Basic.SpherePacking

@[expose] public section

open scoped ENNReal

open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section aux_lemmas

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

end aux_lemmas

section instances

variable {d : ℕ} (S : PeriodicSpherePacking d)

open scoped Pointwise

instance (S : PeriodicSpherePacking 0) : Subsingleton S.centers := sorry

instance (S : PeriodicSpherePacking 0) : Finite S.centers := sorry

include d S in
noncomputable instance PeriodicSpherePacking.finiteOrbitRelQuotient :
    Finite (Quotient S.addAction.orbitRel) := sorry

noncomputable instance : Fintype (Quotient S.addAction.orbitRel) :=
  Fintype.ofFinite _

end instances

section numReps

open scoped Pointwise

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

noncomputable instance PeriodicSpherePacking.instCentersSetoid : Setoid S.centers :=
  S.addAction.orbitRel

noncomputable def PeriodicSpherePacking.numReps : ℕ :=
  Fintype.card (Quotient S.addAction.orbitRel)

end numReps

section numReps_aux

variable {d : ℕ}

end numReps_aux

section theorem_2_3

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

open scoped Pointwise

end theorem_2_3

section theorem_2_2

open scoped Pointwise

variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)

omit d S D L R ι in
instance (E : Type*) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] [Module ℤ E]
    [Module ℝ E] (μ : Measure E) [μ.IsAddLeftInvariant] [IsScalarTower ℤ ℝ E] (s : Submodule ℤ E) :
    VAddInvariantMeasure s E μ := sorry

open ZSpan

variable (b : Basis ι ℤ S.lattice)

section finiteDensity_limit

open MeasureTheory Measure Metric ZSpan

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

open Filter Topology

section VolumeBallRatio

open scoped Topology NNReal

open Asymptotics Filter ENNReal EuclideanSpace

end VolumeBallRatio

section DensityEqFdDensity

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

end DensityEqFdDensity

section ConstantEqNormalizedConstant

end ConstantEqNormalizedConstant

section Disjoint_Covering_of_Centers

end Disjoint_Covering_of_Centers

section Fundamental_Domains_in_terms_of_Basis

open Submodule

variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)

end Fundamental_Domains_in_terms_of_Basis

section Periodic_Density_Formula

noncomputable instance HDivENNReal : HDiv NNReal ENNReal ENNReal where
  hDiv := fun x y => x / y

noncomputable instance HMulENNReal : HMul NNReal ENNReal ENNReal where
  hMul := fun x y => x * y

end Periodic_Density_Formula

section Empty_Centers

end Empty_Centers

section Periodic_Constant_Eq_Constant

end Periodic_Constant_Eq_Constant

end finiteDensity_limit

end theorem_2_2
