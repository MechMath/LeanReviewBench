module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Factors
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.FLT.Four
public import Mathlib.NumberTheory.FLT.Three
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.ModCases

@[expose] public section

/--
A *Frey Package* is a 4-tuple (a,b,c,p) of integers
satisfying $a^p+b^p=c^p$ and some other inequalities
and congruences. These facts guarantee that all of
the all the results in section 4.1 of Serre's paper [serre]
apply to the corresponding Frey curve, the
elliptic curve $Y^2=X(X-a^p)(X+b^p).$
In particular the $p$-torsion of this curve is a highly
suspicious object. Serre could already prove in 1987
(using Mazur's theorem) that the $p$-torsion had to be
an irreducible Galois representation; in 1990 Ribet
proved that the $p$-torsion could not be irreducible,
assuming modularity of the Frey curve. In 1993 Wiles
showed that the Frey curve was modular, completing the
proof.
-/
structure FreyPackage where
  /-- The integer `a` in the Frey package. -/
  a : ℤ
  /-- The integer `b` in the Frey package. -/
  b : ℤ
  /-- The integer `c` in the Frey package. -/
  c : ℤ
  /-- The integer `a` is nonzero. -/
  ha0 : a ≠ 0
  /-- The integer `b` is nonzero. -/
  hb0 : b ≠ 0
  /-- The integer `c` is nonzero. -/
  hc0 : c ≠ 0
  /-- The prime number `p` in the Frey package. -/
  p : ℕ
  /-- The natural number `p` is prime. -/
  pp : Nat.Prime p
  /-- The prime `p` is at least `5`. -/
  hp5 : 5 ≤ p
  /-- The Fermat equation `a ^ p + b ^ p = c ^ p` holds. -/
  hFLT : a ^ p + b ^ p = c ^ p
  /-- The integers `a` and `b` are coprime. Together with `hFLT` this is
  equivalent to `a`, `b` and `c` being pairwise coprime. -/
  hgcdab : gcd a b = 1
  /-- The integer `a` is congruent to `3` modulo `4`. -/
  ha4 : (a : ZMod 4) = 3
  /-- The integer `b` is even, i.e. congruent to `0` modulo `2`. -/
  hb2 : (b : ZMod 2) = 0

namespace FreyPackage

/-- Given a counterexample a^p+b^p=c^p to Fermat's Last Theorem with p>=5
    and prime, there exists a Frey package. -/
lemma of_not_FermatLastTheoremFor_p_ge_5
    {p : ℕ} (pp : p.Prime) (hp5 : 5 ≤ p) (H : ¬ FermatLastTheoremFor p) :
    Nonempty FreyPackage := sorry

end FreyPackage
