module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

@[expose] public section

/-- A class encoding the product scalar multiplication of `∀ b : β, R b` on `∀ a : α, M a`
that is determined by the fibers of a supplied function `f : α → β` on indices.
Specifically, if `f a = b`, then `(r • x) a = r b • x a` for any `r : ∀ b, R b` and
`x : ∀ a, M a`. -/
class Pi.FiberwiseSMul {α β : Type*} (f : α → β) (R : β → Type*) (M : α → Type*)
    [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (M a)]
    [(b : β) → (σ : {a // f a = b}) → Module (R b) (M σ)]
    [Module ((b : β) → R b) ((a : α) → M a)] : Prop where
  map_smul (f R M) (r : (b : β) → R b) (x : (a : α) → M a) (b : β) (σ : {a // f a = b}) :
    (r • x) σ = r b • x σ

/-- A class encoding the product scalar multiplication of `R × S` on `M × N` of the format
`x • y = (x.1 • y.1, x.2 • y.2)`. Use this as an assumption instead of constructing
the `R × S` action on `M × N`. -/
class Prod.IsProdSMul (R S M N : Type*) [SMul R M] [SMul S N] [SMul (R × S) (M × N)] : Prop where
  map_smul (x : R × S) (y : M × N)  : x • y = (x.1 • y.1, x.2 • y.2)

open scoped RestrictedProduct in
/-- A class encoding the product scalar multiplication of `Πʳ b, [R b, A b]_[𝓕]` on
`Πʳ a, [M a, B a]_[𝓖]` that is determined by the fibers of a supplied function `f : α → β` on
indices. Specifically, if `f a = b`, then `(r • x) a = r b • x a` for any `r : ∀ b, R b` and
`x : ∀ a, M a`. This is `Pi.FiberwiseSMul` for restricted products. -/
class RestrictedProduct.FiberwiseSMul {α β : Type*} (f : α → β) (R : (b : β) → Type*)
    (A : (b : β) → Set (R b)) (𝓕 : Filter β) (M : (a : α) → Type*) (B : (a : α) → Set (M a))
    (𝓖 : Filter α) [(b : β) → (σ : { a // f a = b }) → SMul (R b) (M ↑σ)]
    [SMul (Πʳ b, [R b, A b]_[𝓕]) (Πʳ a, [M a, B a]_[𝓖])] : Prop where
  map_smul (r : Πʳ b, [R b, A b]_[𝓕]) (x : Πʳ a, [M a, B a]_[𝓖]) (b : β)
    (σ : {a // f a = b}) : (r • x) σ = r b • x σ
