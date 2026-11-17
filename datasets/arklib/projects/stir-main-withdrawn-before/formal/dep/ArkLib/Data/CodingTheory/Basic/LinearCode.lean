module

public import Batteries.Data.Fin.Fold
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.Pointwise
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Qify
public import Mathlib.Topology.MetricSpace.Infsep
public import dep.ArkLib.Data.CodingTheory.Basic.Distance
public import dep.ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import dep.ArkLib.Data.CodingTheory.Prelims
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code

noncomputable section

section

variable {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]

open Finset

end

end

end Code

variable [Finite R]

open Fintype

/-- A `ModuleCode ι F A` is an `F`-linear code of length indexed by `ι` over the alphabet `A`,
defined as an `F`-submodule of `ι → A`. -/
@[simp]
abbrev ModuleCode.{u, v, w} (ι : Type u) (F : Type v) [Semiring F] -- ModuleCode ι F A
    (A : Type w) [AddCommMonoid A] [Module F A] : Type (max u w) := Submodule F (ι → A)

abbrev LinearCode.{u, v} (ι : Type u) [Fintype ι] (F : Type v) [Semiring F] : Type (max u v) :=
  Submodule F (ι → F)

namespace LinearCode

section

variable {F : Type*} {A : Type*} [AddCommMonoid A]
         {ι : Type*} [Fintype ι]
         {κ : Type*} [Fintype κ]

/--
The dimension of a linear code.
-/
noncomputable def dim [Semiring F] {A : Type*} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) : ℕ := Module.finrank F MC

/--
The length of a linear code.
-/
def length [Semiring F] {A : Type*} [AddCommMonoid A] [Module F A]
    (_ : ModuleCode ι F A) : ℕ :=
  Fintype.card ι

/--
The **base-field-dimension rate** of a code: `dim MC / |ι|`, the `F`-dimension of the code
divided by the block length alone.

Over the field alphabet itself (`A = F`) this is the usual rate `ρ = k/n`. Over a module
alphabet `A = F^s` it is *not* the alphabet-normalized rate `log_{|A|} |C| / n = dim/(s*n)`,
since it never divides by the alphabet dimension `s`; that normalization is `alphabetRate`
below.
-/
noncomputable def rate [Semiring F] {A : Type*} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) : ℚ≥0 :=
  (dim MC : ℚ≥0) / length MC

/--
  `ρ LC` is the rate of the linear code `LC`.

  Uses `&` to make the notation non-reserved, allowing `ρ` to also be used as a variable name.
-/
scoped syntax &"ρ" term : term

scoped macro_rules
  | `(ρ $t:term) => `(LinearCode.rate $t)

open Submodule

end

section

variable {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]
         {A : Type*} [AddCommMonoid A] [DecidableEq A]

end

section Computable

end Computable

end LinearCode
