module

public import Batteries.Data.Fin.Fold
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Ring.GeomSum
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
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.Pointwise
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Qify
public import Mathlib.Topology.MetricSpace.Infsep
public import dep.ArkLib.Data.CodingTheory.Basic.Distance
public import dep.ArkLib.Data.CodingTheory.Basic.LinearCode
public import dep.ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import dep.ArkLib.Data.CodingTheory.Prelims
public import dep.ArkLib.Data.MvPolynomial.Interpolation
public import dep.ArkLib.Data.MvPolynomial.Multilinear
public import dep.CompPoly.Data.Classes.DCast
public import dep.CompPoly.Data.MvPolynomial.Notation
public import dep.CompPoly.ToMathlib.Finsupp.Fin
public import dep.CompPoly.ToMathlib.MvPolynomial.Equiv

@[expose] public section

namespace ReedSolomon

open Polynomial NNReal

variable {F : Type*} {ι : Type*} (domain : ι ↪ F)

/-- The evaluation of a polynomial at a set of points specified by `domain : ι ↪ F`, as a linear
map. -/
def evalOnPoints [Semiring F] : F[X] →ₗ[F] (ι → F) where
  toFun p x := p.eval (domain x)
  map_add'  := sorry
  map_smul' := sorry

/-- The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `domain`.
-/
noncomputable def code (deg : ℕ) [Semiring F] : Submodule F (ι → F) :=
  (Polynomial.degreeLT F deg).map (evalOnPoints domain)

open Polynomial Matrix Code LinearCode

variable {F ι ι' : Type*}
         {C : Set (ι → F)}

section

open Finset Function

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [Field F] [Fintype F]

abbrev RScodeSet (domain : ι ↪ F) (deg : ℕ) : Set (ι → F) := ReedSolomon.code domain deg

open Classical in
noncomputable def toFinset (domain : ι ↪ F) (deg : ℕ) : Finset (ι → F) :=
  (RScodeSet domain deg).toFinset

end

section

variable {deg m n : ℕ} {α : Fin m → F}

section

variable [Semiring F] {p : F[X]}

end

open LinearCode

section

variable [Semiring F]

end

section

open NNReal

variable [Field F]

end

section

variable [Semiring F] {x : F} [Fintype ι] {α : ι ↪ F}

end

/-- A Reed–Solomon code of positive dimension over a nonempty domain has a nonzero codeword. -/
instance instNontrivial [Field F] [NeZero n] [Nonempty ι] {α : ι ↪ F} :
    Nontrivial (ReedSolomon.code α n) := sorry

end

noncomputable scoped instance {α : Type} (s : Set α) [inst : Finite s] : Fintype s :=
  Fintype.ofFinite _

section

open LinearMap Finset Polynomial

variable {F : Type*} [Field F]
         {ι : Type*} [Fintype ι] [DecidableEq ι]
         {domain : ι ↪ F}
         {deg : ℕ}

variable {F : Type*} [Semiring F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- A domain `ι ↪ F` is `smooth`, if `ι ⊆ F`, `|ι| = 2^k` for some `k` and there exists a subgroup
 `H` in the group of units `Rˣ` and an invertible element `a ∈ R` such that `ι = a • H` -/
class Smooth
  (domain : ι ↪ F) where
    H : Subgroup (Units F)
    a           : Units F
    h_coset     : Finset.image domain Finset.univ
                  = (fun h : Units F => (a : F) * (h : F)) '' (H : Set (Units F))
    h_card_pow2 : ∃ k : ℕ, Fintype.card ι = 2 ^ k

end

end ReedSolomon
