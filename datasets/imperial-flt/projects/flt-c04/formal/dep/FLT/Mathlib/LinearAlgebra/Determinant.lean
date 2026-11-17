module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Logic.Equiv.PartialEquiv
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
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.Hacks.RightActionInstances
public import dep.FLT.Mathlib.Algebra.Algebra.Bilinear
public import dep.FLT.Mathlib.Algebra.Algebra.Hom
public import dep.FLT.Mathlib.Algebra.Algebra.Tower
public import dep.FLT.Mathlib.RingTheory.SimpleRing.TensorProduct
public import dep.FLT.Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

variable (k : Type*) [Field k] {D : Type*} [Ring D] [Algebra k D]

open scoped TensorProduct

variable [Algebra.IsCentral k D] [IsSimpleRing D] [FiniteDimensional k D]

/-- This is instance is in a repo on brauergroup which has been PRed into mathlib
at https://github.com/leanprover-community/mathlib4/pull/26377 .
  The associated FLT issue is #631.
  For now it's in `import dep.FLT.Mathlib.RingTheory.SimpleRing.TensorProduct`.
-/
instance (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B] : IsSimpleRing (B ⊗[k] A) := sorry

instance (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B] : IsSimpleRing (A ⊗[k] B) := sorry

section LinearEquiv

variable {F : Type*} [CommRing F]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {V : Type*} [AddCommGroup V] [Module F V]

end LinearEquiv
