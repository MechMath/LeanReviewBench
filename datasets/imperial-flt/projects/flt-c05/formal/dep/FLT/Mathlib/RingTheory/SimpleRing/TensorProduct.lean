module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Instances
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

@[expose] public section

section some_other_files

namespace TwoSidedIdeal

end TwoSidedIdeal

end some_other_files

@[expose] public section

variable (K A B : Type*) [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

open TensorProduct Module

instance TensorProduct.simple {A B : Type*} [Ring A] [IsSimpleRing A] [Algebra K A] [Ring B]
    [Algebra K B] [Algebra.IsCentral K A] [isSimple_B : IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := sorry
