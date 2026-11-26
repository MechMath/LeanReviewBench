module

public import Mathlib.RingTheory.AlgebraTower

@[expose] public section

/-- If `f : A → B` where `A` and `B` are both `R`- and `S`-modules, then `IsBiscalar R S f`
asserts that `f` satisfies the linear scalar property for both `R` and `S`. I.e.,
- `f (r • a) = r • f a`
- `f (s • a) = s • f a`
for all `r : R`, `s : S`, `a : A`.

Note that this is symmetric in its arguments and only takes in a function as input. For bundled
functions already containing a scalar, this class can be used to assert that the function
also has another scalar. The convention in this repo is to use the bundled scalar as the first
argument. For example, if `f : A →ₗ[R] B` and it is also scalar with respect to `S`, then
use `IsBiscalar R S f`. -/
class IsBiscalar (R S : Type*) {A B : Type*} [Semiring R] [Semiring S] [AddCommMonoid A]
    [AddCommMonoid B] [Module R A] [Module R B] [Module S A] [Module S B] (f : A → B) where
  map_smul₁ : ∀ (r : R) (a : A), f (r • a) = r • f a
  map_smul₂ : ∀ (s : S) (a : A), f (s • a) = s • f a

section linear

variable {A B : Type*} (S' : Type*) {S : Type*}
    [Semiring S'] [Semiring S] [AddCommMonoid A] [AddCommMonoid B] [Module S A]
    [Module S B] [Module S' A] [Module S' B]

/--
Given a linear map `f : A →ₗ[S] B` which also satisfies `f (s' • a) = s' • f a` for `s : S'`,
with both `S` and `S'` sharing a common base ring `R`, then `f.changeScalars R S'` returns `f`
viewed as an `S'`-algebra homomorphism.
-/
def LinearMap.changeScalars (f : A →ₗ[S] B) [IsBiscalar S S' f] :
    A →ₗ[S'] B where
  __ := f
  map_smul' s x := sorry

/--
Given a linear isomorphism `f : A ≃ₗ[S] B` which also satisfies `f (s' • a) = s' • f a` for
`s : S'`, with both `S` and `S'` sharing a common base ring `R`, then `f.changeScalars R S'`
returns `f` viewed as an `S'`-algebra isomorphism.
-/
def LinearEquiv.changeScalars (f : A ≃ₗ[S] B) [IsBiscalar S S' f] :
    A ≃ₗ[S'] B where
  __ := LinearMap.changeScalars S' f.toLinearMap
  invFun := f.invFun
  left_inv (a : A) := sorry
  right_inv (b : B) := sorry

end linear

section algebra

theorem IsBiscalar.commutes {S : Type*} (S' : Type*) {A B : Type*} [CommSemiring S']
    [CommSemiring S] [Semiring A] [Semiring B] [Algebra S' A] [Algebra S' B] [Algebra S A]
    [Algebra S B] (f : A →ₐ[S] B) [IsBiscalar S S' f] (s : S') :
    f (algebraMap S' A s) = algebraMap S' B s := sorry

variable {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B]

/--
Produces an `S'`-linear algebra map from an `S`-linear algebra map `f : A →ₐ[S] B` which also
has scalars `S'`.
-/
def AlgHom.changeScalars (f : A →ₐ[S] B) [IsBiscalar S S' f] :
    A →ₐ[S'] B where
  __ := f
  commutes' (r : _) := sorry

/--
Produces an `S'`-linear algebra isomorphism from an `S`-linear algebra isomorphism `f : A ≃ₐ[S] B`
which also has scalars `S'`.
-/
def AlgEquiv.changeScalars (f : A ≃ₐ[S] B) [IsBiscalar S S' f.toAlgHom] :
    A ≃ₐ[S'] B where
  __ := AlgHom.changeScalars S' f.toAlgHom
  invFun := f.invFun
  left_inv (a : A) := sorry
  right_inv (b : B) := sorry
  commutes' := fun _ => sorry

end algebra

section diamond_checks

end diamond_checks
