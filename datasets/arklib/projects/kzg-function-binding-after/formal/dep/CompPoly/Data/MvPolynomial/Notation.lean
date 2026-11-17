module

public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import dep.CompPoly.ToMathlib.Finsupp.Fin
public import dep.CompPoly.ToMathlib.MvPolynomial.Equiv

@[expose] public section

noncomputable section

namespace MvPolynomial

section Equiv

variable (R : Type*) [CommSemiring R] {n : ℕ}

end Equiv

end MvPolynomial

end

open MvPolynomial

@[inherit_doc] scoped[Polynomial] notation:9000 R "⦃< " d "⦄[X]" => Polynomial.degreeLT R d

@[inherit_doc] scoped[Polynomial] notation:9000 R "⦃≤ " d "⦄[X]" => Polynomial.degreeLE R d

@[inherit_doc] scoped[MvPolynomial] notation:9000 R "[X " σ "]"  => MvPolynomial σ R

@[inherit_doc] scoped[MvPolynomial] notation:9000
  R "⦃≤ " d "⦄[X " σ "]"  => MvPolynomial.restrictDegree σ R d

notation:70 s:70 " ^^ " t:71 => Fintype.piFinset fun (i : t) ↦ s i

notation:70 s:70 " ^ᶠ " t:71 => Fintype.piFinset fun (i : Fin t) ↦ s

/--
  Notation for multivariate polynomial evaluation. The expression `p ⸨x_1, ..., x_n⸩` is expanded to
  the evaluation of `p` at the concatenated vectors `x_1, ..., x_n`, with the casting handled by
  `omega`. If `omega` fails, we can specify the proof manually using `'proof` syntax.

  For example, `p ⸨x, y, z⸩` is expanded to
    `MvPolynomial.eval (Fin.append (Fin.append x y) z ∘ Fin.cast (by omega)) p`.
-/
syntax:max (name := mvEval) term "⸨" term,* "⸩" : term

macro_rules (kind := mvEval)
  | `($p⸨$x⸩) => `(MvPolynomial.eval ($x ∘ Fin.cast (by omega)) $p)
  | `($p⸨$x, $y⸩) => `(MvPolynomial.eval (Fin.append $x $y ∘ Fin.cast (by omega)) $p)
  | `($p⸨$x, $y, $z⸩) =>
      `(MvPolynomial.eval (Fin.append (Fin.append $x $y) $z ∘ Fin.cast (by omega)) $p)

@[inherit_doc mvEval]
syntax (name := mvEval') term "⸨" term,* "⸩'" term:max : term

macro_rules (kind := mvEval')
  | `($p⸨$x⸩'$h) => `(MvPolynomial.eval ($x ∘ Fin.cast $h) $p)
  | `($p⸨$x, $y⸩'$h) => `(MvPolynomial.eval (Fin.append $x $y ∘ Fin.cast $h) $p)
  | `($p⸨$x, $y, $z⸩'$h) =>
      `(MvPolynomial.eval (Fin.append (Fin.append $x $y) $z ∘ Fin.cast $h) $p)

/--
  Notation for evaluating a multivariate polynomial with one variable left intact. The expression `p
  ⸨X ⦃i⦄, x_1, ..., x_n⸩` is expanded to the evaluation of `p`, viewed as a multivariate polynomial
  in all but the `i`-th variable, on the vector that is the concatenation of `x_1, ..., x_n`.
  Similar to `mvEval` syntax, casting between `Fin` types is handled by `omega`, or manually
  specified using `'proof` syntax.

  For example, `p ⸨X ⦃i⦄, x, y⸩` is expanded to `Polynomial.map (MvPolynomial.eval (Fin.append x y ∘
    Fin.cast (by omega)))` `(MvPolynomial.finSuccEquivNth i p)`.
-/
syntax (name := mvEvalToPolynomial) term "⸨X " "⦃" term "⦄" "," term,* "⸩" : term

macro_rules (kind := mvEvalToPolynomial)
  | `($p⸨X ⦃$i⦄, $x⸩) =>
      `(Polynomial.map (MvPolynomial.eval ($x ∘ Fin.cast (by omega)))
        (MvPolynomial.finSuccEquivNth _ $i $p))
  | `($p⸨X ⦃$i⦄, $x, $y⸩) =>
      `(Polynomial.map (MvPolynomial.eval (Fin.append $x $y ∘ Fin.cast (by omega)))
        (MvPolynomial.finSuccEquivNth _ $i $p))
  | `($p⸨X ⦃$i⦄, $x, $y, $z⸩) =>
      `(Polynomial.map (MvPolynomial.eval (Fin.append (Fin.append $x $y) $z ∘ Fin.cast (by omega)))
        (MvPolynomial.finSuccEquivNth _ $i $p))

@[inherit_doc mvEvalToPolynomial]
syntax (name := mvEvalToPolynomial') term "⸨X " "⦃" term "⦄" "," term,* "⸩'" term:max : term

macro_rules (kind := mvEvalToPolynomial')
  | `($p⸨X ⦃$i⦄, $x⸩'$h) =>
      `(Polynomial.map (MvPolynomial.eval ($x ∘ Fin.cast $h))
        (MvPolynomial.finSuccEquivNth _ $i $p))
  | `($p⸨X ⦃$i⦄, $x, $y⸩'$h) =>
      `(Polynomial.map (MvPolynomial.eval (Fin.append $x $y ∘ Fin.cast $h))
        (MvPolynomial.finSuccEquivNth _ $i $p))
  | `($p⸨X ⦃$i⦄, $x, $y, $z⸩'$h) =>
      `(Polynomial.map (MvPolynomial.eval (Fin.append (Fin.append $x $y) $z ∘ Fin.cast $h))
        (MvPolynomial.finSuccEquivNth _ $i $p))
