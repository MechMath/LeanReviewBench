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
public import dep.ArkLib.Data.CodingTheory.Prelims
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code

open NNReal

notation "Δ₀(" u ", " v ")" => hammingDist u v

notation "‖" u "‖₀" => hammingNorm u

section Agreement

variable {u v : n → R}

end Agreement

/-- The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct
  elements of the code.
We formalize this as the infimum `sInf` over all `d : ℕ` such that there exist `u v : n → R` in the
code with `u ≠ v` and `hammingDist u v ≤ d`. If none exists, then we define the distance to be `0`.
-/
noncomputable def dist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ Δ₀( u, v ) ≤ d}

instance : EDist (n → R) where
  edist := fun u v => hammingDist u v

instance : Dist (n → R) where
  dist := fun u v => hammingDist u v

notation "‖" C "‖₀" => dist C

/-- The distance from a vector `u` to a code `C` is the minimum Hamming distance between `u`
and any element of `C`. -/
noncomputable def distFromCode (u : n → R) (C : Set (n → R)) : ℕ∞ :=
  sInf {d | ∃ v ∈ C, hammingDist u v ≤ d}

notation "Δ₀(" u ", " C ")" => distFromCode u C

section Agreement

variable {u v : n → R}

section Counting

variable {T : Finset (n → R)}

end Counting

end Agreement

section Computable

/-- Computable version of the Hamming distance of a code `C`, assuming `C` is a `Fintype`.

The return type is `ℕ∞` since we use `Finset.min`. -/
def dist' (C : Set (n → R)) [Fintype C] : ℕ∞ :=
  Finset.min <| ((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2)).image
    (fun ⟨u, v⟩ => hammingDist u.1 v.1)

notation "‖" C "‖₀'" => dist' C

variable {C : Set (n → R)} [Fintype C]

section

variable {α : Type*}
         {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- The set of possible distances `δf` from a vector `w` to a code `C`.
-/
def possibleDistsToCode (w : ι → F) (C : Set (ι → F)) (δf : (ι → F) → (ι → F) → α) : Set α :=
  {d : α | ∃ c ∈ C, c ≠ w ∧ δf w c = d}

/-- The set of possible distances `δf` between distinct codewords in a code `C`.

  - TODO: This allows us to express distance in non-ℝ, which is quite convenient.
          Extending to `(E)Dist` forces this into `ℝ`; give some thought.
-/
def possibleDists (C : Set (ι → F)) (δf : (ι → F) → (ι → F) → α) : Set α :=
  {d : α | ∃ p ∈ Set.offDiag C, δf p.1 p.2 = d}

end

/-- Computable version of the distance from a vector `u` to a finite code `C`. -/
def distFromCode' (C : Set (n → R)) [Fintype C] (u : n → R) : ℕ∞ :=
  Finset.min <| (@Finset.univ C _).image (fun v => hammingDist u v.1)

notation "Δ₀'(" u ", " C ")" => distFromCode' C u

end Computable

end Code
