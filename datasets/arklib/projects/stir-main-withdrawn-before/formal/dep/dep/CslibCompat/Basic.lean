module

public import Cslib.Init
public import Mathlib.Data.PFunctor.Univariate.Basic

@[expose] public section

universe uA uB uA₁ uA₂ uB₁ uB₂

namespace PFunctor

/-- Two polynomial functors are equal if their head types are equal and their child types
agree over that equality. -/
@[ext (iff := false)]
theorem ext {P Q : PFunctor.{uA, uB}} (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) :
    P = Q := sorry

section monomial

/-- The monomial `PFunctor` with head type `A` and constant `B` for any `a : A`. -/
abbrev monomial (A : Type uA) (B : Type uB) : PFunctor := ⟨A, fun _ => B⟩

@[inherit_doc] scoped[PFunctor] infixr:82 " y^ " => monomial

end monomial

section zero

/-- The zero polynomial functor, defined as `A = PEmpty` and `B _ = PEmpty`, is the identity with
respect to sum (up to equivalence). -/
@[simps] instance instZeroPFunctor : Zero PFunctor where zero := monomial PEmpty PEmpty

instance instIsEmptyZeroPFunctor : IsEmpty (0 : PFunctor.{uA, 0}).A := sorry

end zero

section one

/-- The unit polynomial functor, defined as `A = PUnit` and `B _ = PEmpty`, is the identity with
respect to product (up to equivalence). -/
@[simps] instance instOnePFunctor : One PFunctor where one := monomial PUnit PEmpty

instance instUniqueOneA : Unique (1 : PFunctor.{uA, 0}).A := inferInstanceAs (Unique PUnit)

instance instIsEmptyOneB (a : (1 : PFunctor.{uA, uB}).A) : IsEmpty ((1 : PFunctor.{uA, uB}).B a) := sorry

end one

/-- The constant polynomial functor `P(y) = A y^ PEmpty = A`. -/
abbrev C (A : Type uA) : PFunctor := monomial A PEmpty

/-- The linear polynomial functor `P(y) = A y`. -/
abbrev linear (A : Type uA) : PFunctor := monomial A PUnit

/-- The pure-power polynomial functor `y^ B`, representable on `B`. -/
abbrev purePower (B : Type uB) : PFunctor := monomial PUnit B

@[inherit_doc purePower] scoped[PFunctor] notation:100 "y^" B:100 => purePower B

/-- The indeterminate polynomial functor `P(y) = y`, the identity with respect to
composition and tensor product (up to equivalence). -/
abbrev y : PFunctor := monomial PUnit PUnit

section add

/-- The sum of two polynomial functors `P` and `Q`, written as `P + Q`,
defined as the sum of the head types and the dependent sum recursor for the child types.

The child universes must agree. The named spelling `P.add Q` can elaborate in contexts where
`P + Q` fails to infer universes, such as under `PFunctor.W`; see `CslibTests.PFunctor`. -/
@[implicit_reducible] def add (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} :=
  ⟨P.A ⊕ Q.A, @Sum.rec P.A Q.A (fun _ => Type uB) P.B Q.B⟩

@[simps!] instance instHAddPFunctor :
    HAdd PFunctor.{uA₁, uB} PFunctor.{uA₂, uB} PFunctor.{max uA₁ uA₂, uB} where
  hAdd := add

end add

section prod

/-- The product of two polynomial functors `P` and `Q`, written as `P * Q`,
defined as the product of the head types and the sum of the child types. -/
@[implicit_reducible] def prod (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} := ⟨P.A × Q.A, fun ab => P.B ab.1 ⊕ Q.B ab.2⟩

@[simps!] instance instHMulPFunctor :
    HMul PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{max uA₁ uA₂, max uB₁ uB₂} where
  hMul := prod

end prod

section Unary

/-- A polynomial functor is unary if all child types have exactly one element. -/
class Unary (P : PFunctor) where
  unary (a : P.A) : Unique (P.B a)

attribute [instance_reducible, instance] PFunctor.Unary.unary

/-- A polynomial functor has children with decidable equality. -/
class DecidableEqChildren (P : PFunctor) where
  decidableEq (a : P.A) : DecidableEq (P.B a)

attribute [instance_reducible, instance] DecidableEqChildren.decidableEq

/-- A unary polynomial functor has decidable child equality. -/
instance (P : PFunctor) [P.Unary] : P.DecidableEqChildren where
  decidableEq _ _ _ := isTrue (Subsingleton.elim _ _)

instance (A : Type uA) : (linear.{uA, uB} A).Unary where
  unary _ := inferInstanceAs (Unique PUnit)

end Unary

end PFunctor
