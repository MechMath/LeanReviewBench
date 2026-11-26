module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

open scoped TensorProduct

instance (k A B : Type*) [Field k] [CommRing A] [Ring B]
    [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] :
    Algebra.IsCentral A (A ⊗[k] B) := sorry
