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
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.Pointwise
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Qify
public import Mathlib.Topology.MetricSpace.Infsep
public import dep.ArkLib.Data.CodingTheory.Basic.Distance
public import dep.ArkLib.Data.CodingTheory.Prelims
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code

noncomputable section

open NNReal

open scoped NNReal

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {u v w c : ι → F}
         {C : Set (ι → F)}

section

variable [Nonempty ι] [DecidableEq F]

def relHammingDist (u v : ι → F) : ℚ≥0 :=
  hammingDist u v / Fintype.card ι

/--
  `δᵣ(u,v)` denotes the relative Hamming distance between vectors `u` and `v`.
-/
notation "δᵣ(" u ", " v ")" => relHammingDist u v

/-- The relative Hamming distance from a vector to a code, defined as the infimum
    of all relative distances from `u` to codewords in `C`.
    The type is `ENNReal` (ℝ≥0∞) to correctly handle the case `C = ∅`.
  For case of Nonempty C, we can use `relDistFromCode (δᵣ')` for smaller value range in
    `ℚ≥0`, which is equal to this definition. -/
noncomputable def relDistFromCode (u : ι → F) (C : Set (ι → F)) : ENNReal :=
  sInf {d | ∃ v ∈ C, (relHammingDist u v) ≤ d}

/-- `δᵣ(u,C)` denotes the relative distance from u to C. This is the main standard definition
used in statements. The NNRat version of it is `δᵣ'(u, C)`. -/
notation "δᵣ(" u ", " C ")" => relDistFromCode u C

/-- Ball of radius `r` centred at a word `y` with respect to the relative Hamming distance. -/
def relHammingBall (y : ι → F) (r : ℝ) : Set (ι → F) :=
  {x | δᵣ(y, x) ≤ r}

end

section

variable [DecidableEq F]

/-- The set of possible distances between distinct codewords in a code.
-/
def possibleRelHammingDists (C : Set (ι → F)) : Set ℚ≥0 :=
  possibleDists C relHammingDist

variable [Nonempty ι]

/-- The set of possible distances between distinct codewords in a code is a finite set.
-/
@[simp]
lemma finite_possibleRelHammingDists : (possibleRelHammingDists C).Finite := sorry

open Classical in
/-- The minimum relative Hamming distance of a code.

Spelled with `Set.Finite.toFinset` rather than `Set.toFinset` under a local `Fintype`
instance. The two are definitionally equal, but only the former lets the `Set.Finite.*`
rewriting API fire, which the characterisation lemmas below need.
-/
def minRelHammingDistCode (C : Set (ι → F)) : ℚ≥0 :=
  if h : (possibleRelHammingDists C).Nonempty
  then finite_possibleRelHammingDists.toFinset.min'
        ((Set.Finite.toFinset_nonempty (hs := finite_possibleRelHammingDists)).mpr h)
  else 0

end

/-- `δᵣ C` denotes the minimum relative Hamming distance of a code `C`.
-/
notation "δᵣ" C => minRelHammingDistCode C

/-- The set of possible relative Hamming distances from a vector to a code is a finite set.
-/
@[simp]
lemma finite_possibleRelHammingDistsToCode [Nonempty ι] [DecidableEq F] :
    (possibleDistsToCode w C relHammingDist).Finite := sorry

instance [Nonempty ι] [DecidableEq F] :
    Fintype (possibleDistsToCode w C relHammingDist) :=
  @Fintype.ofFinite _ finite_possibleRelHammingDistsToCode

/-- Computable version of the relative Hamming distance from a vector `w` to a finite
non-empty code `C`. This one is intended to mimic the definition of `distFromCode'`.
However, **we don't have `ENNRat (ℚ≥0∞)` (as counterpart of `ENat (ℕ∞)` in `distFromCode'`)**
so we require `[Nonempty C]`.
TODO: define `ENNRat (ℚ≥0∞)` so we can migrate both `relDistFromCode`
  and `relDistFromCode'` to `ℚ≥0∞` -/
def relDistFromCode' {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [DecidableEq F]
    (w : ι → F) (C : Set (ι → F)) [Fintype C] [Nonempty C] : ℚ≥0 :=
  Finset.min'
    (Finset.univ.image (fun (c : C) => relHammingDist w c))
    (Finset.univ_nonempty.image _)

/-- `δᵣ'(w,C)` denotes the relative Hamming distance between a vector `w` and a code `C`.
This is a different statement of the generic definition `δᵣ(w,C)`. -/
notation "δᵣ'(" w ", " C ")" => relDistFromCode' w C

end

end Code
