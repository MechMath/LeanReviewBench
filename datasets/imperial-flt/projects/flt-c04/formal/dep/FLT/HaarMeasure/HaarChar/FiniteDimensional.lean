module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TwoSidedIdeal.Instances
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.HaarMeasure.HaarChar.AddEquiv
public import dep.FLT.HaarMeasure.HaarChar.Ring
public import dep.FLT.Hacks.RightActionInstances
public import dep.FLT.Mathlib.Algebra.Algebra.Bilinear
public import dep.FLT.Mathlib.Algebra.Algebra.Hom
public import dep.FLT.Mathlib.Algebra.Algebra.Tower
public import dep.FLT.Mathlib.LinearAlgebra.Determinant
public import dep.FLT.Mathlib.LinearAlgebra.Matrix.Transvection
public import dep.FLT.Mathlib.LinearAlgebra.Pi
public import dep.FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
public import dep.FLT.Mathlib.Order.Filter.Cofinite
public import dep.FLT.Mathlib.RingTheory.SimpleRing.TensorProduct
public import dep.FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Equiv
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

namespace MeasureTheory

open Measure

section HaarMeasureScaling

open Matrix Measure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {F : Type*} [MeasurableSpace F] [TopologicalSpace F]
    [BorelSpace F] [LocallyCompactSpace F]

section commring

variable [CommRing F] [IsTopologicalRing F]

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [Module F V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V]
    [LocallyCompactSpace V]

open Module

end commring

section field

variable [Field F] [IsTopologicalRing F]

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [Module F V] [FiniteDimensional F V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V]
    [LocallyCompactSpace V]

open Module

end field

end HaarMeasureScaling

variable {F : Type*} [Field F] [MeasurableSpace F] [TopologicalSpace F] [BorelSpace F]
  [IsTopologicalRing F] [LocallyCompactSpace F]

section needs_PRing

variable (R : Type*) [CommSemiring R]

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]

variable [Algebra R A]

/--
Multiplication on the left by a unit of an F-algebra which is a topological
ring, is a continuous F-linear homeomorphism.
-/
def _root_.ContinuousLinearEquiv.mulLeft (u : Aˣ) : A ≃L[R] A where
  __ := LinearEquiv.mulLeft R u
  continuous_toFun := continuous_const_mul _
  continuous_invFun := continuous_const_mul _

end needs_PRing

section ring

variable {A : Type*} [Ring A] [TopologicalSpace A]
    [Algebra F A] [FiniteDimensional F A] [IsModuleTopology F A]
    [IsTopologicalRing A] -- can be deduced from previous assumptions but only using F
    [LocallyCompactSpace A] -- can also be proved but only using F
    [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology F]

end ring

section issimplering

variable {D : Type*} [Ring D] [TopologicalSpace D]
    [Algebra F D] [FiniteDimensional F D] [IsSimpleRing D]
    [IsModuleTopology F D]
    [Algebra.IsCentral F D] -- could be removed if necessary by proving
    -- `IsSimpleRing.mulLeft_det_eq_mulRight_det` with tensoring over the center of `D`
    -- instead of `k`.
    [IsTopologicalRing D] -- can be deduced from previous assumptions but only using F
    [LocallyCompactSpace D] -- can also be proved but only using F
    [MeasurableSpace D] [BorelSpace D]
    [SecondCountableTopology F]

end issimplering

end MeasureTheory
