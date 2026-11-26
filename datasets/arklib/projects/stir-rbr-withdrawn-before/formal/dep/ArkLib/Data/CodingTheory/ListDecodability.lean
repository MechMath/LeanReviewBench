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
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Lemmas
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
public import Mathlib.Data.Set.Finite.Basic
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
public import dep.ArkLib.Data.CodingTheory.Basic.LinearCode
public import dep.ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import dep.ArkLib.Data.CodingTheory.Prelims
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

namespace Code

open scoped NNReal

section

variable {ι : Type*} [Fintype ι]
         {F : Type*}

open Classical in
/-- The set of `r`-close codewords to a given word `y` with respect to the relative Hamming
distance.
Note that this is exactly `Λ (C, y, r)` from [ACFY24] and ` List (C, y, r)` from [ACFY24stir]. -/
def closeCodewordsRel (C : Set (ι → F)) (y : ι → F) (r : ℝ) : Set (ι → F) :=
  {c | c ∈ C ∧ c ∈ Code.relHammingBall y r}

/-- The maximised point-list size of `C` at radius `δ`: the supremum over words `f` of the
cardinality of `closeCodewordsRel C f δ`.

Note that this is the *size*; the point list itself is `closeCodewordsRel`.

Being `ℕ∞`-valued, an infinite point list contributes `⊤` rather than the `0` that `Set.ncard`
would give, so a finite bound implies finiteness rather than assuming it
(`finite_closeCodewordsRel_of_Lambda_le`).

The radius is an unrestricted `ℝ`: `Lambda` is total in it, taking value `0` below `0` where the
ball is empty. Since relative Hamming distance is `1/|ι|`-quantised (`relHammingDistRange`),
`Lambda C` is a step function of `δ`, constant on each `[k/n, (k+1)/n)`. -/
noncomputable def Lambda (C : Set (ι → F)) (δ : ℝ) : ℕ∞ :=
  ⨆ f : ι → F, (closeCodewordsRel C f δ).encard

/-- A code `C` is `(r, ℓ)`-**list decodable** if every point list at relative radius `r` has at
most `ℓ` codewords, that is, `Lambda C r ≤ ⌊ℓ⌋₊`.

Flooring loses nothing, `Lambda` being integer-valued (`isListDecodable_iff_forall_ncard_le`), and
point-list finiteness is implied rather than asserted.

This is a `def`, not an `abbrev`, and so is semireducible: `exact`, `refine` and `apply` see through
it to the `Lambda` inequality, while `simp` and `rw` need `isListDecodable_iff_Lambda_le`. -/
def IsListDecodable (C : Set (ι → F)) (r : ℝ) (ℓ : ℝ≥0) : Prop :=
  Lambda C r ≤ (⌊ℓ⌋₊ : ℕ∞)

end

end Code
