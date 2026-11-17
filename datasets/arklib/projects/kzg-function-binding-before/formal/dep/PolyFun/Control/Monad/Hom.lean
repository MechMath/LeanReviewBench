module

public import Mathlib.Control.Monad.Basic

@[expose] public section

universe u v w x y

variable {m : Type u → Type v} {n : Type u → Type w}

/-- A `NatHom m n` for two functors `m` and `n` is a map `m α → n α` for each possible type `α`.
This is exactly an element of the category `m ⟶ n`, but that has more restricted universes -/
structure NatHom (m : Type u → Type v) (n : Type u → Type w) where
  /-- The underlying family of maps `m α → n α`, one for each type `α`. -/
  toFun : (α : Type u) → m α → n α

/-- `f mx` notation for `NatHom m n` applied to an element of `m α`, with implicit `α` inferred. -/
instance : CoeFun (NatHom m n) (fun _f => {α : Type u} → m α → n α) where
  coe f {α} x := f.toFun α x

/-- A `MonadHom m n` bundles a monad map `m ⟶ n` (represented as a `NatHom`) with proofs that
it respects the `bind` and `pure` operations in the underlying monad. -/
@[ext] structure MonadHom (m : Type u → Type v) [Pure m] [Bind m]
    (n : Type u → Type w) [Pure n] [Bind n] extends NatHom m n where
  toFun_pure' {α} (x : α) : toFun α (pure x) = pure x
  toFun_bind' {α β} (x : m α) (y : α → m β) :
    toFun β (x >>= y) = toFun α x >>= fun x => toFun β (y x)

@[inherit_doc] infixr:25 " →ᵐ " => MonadHom

attribute [simp, grind =] MonadHom.toFun_pure' MonadHom.toFun_bind'

/-- `F mx` notation for `m →ᵐ n` applied to an element of `m α`, with implicit `α` inferred. -/
instance {m : Type u → Type v} [Pure m] [Bind m] {n : Type u → Type w} [Pure n] [Bind n] :
    CoeFun (m →ᵐ n) (fun _f => {α : Type u} → m α → n α) where
  coe f {α} x := f.toFun α x

namespace MonadHom

variable {m : Type u → Type v} [Monad m]
  {n : Type u → Type w} [Monad n]
  {n' : Type u → Type x} [Monad n']
  {n'' : Type u → Type y} [Monad n'']
  {α β γ : Type u}

/-- The identity morphism between a monad and itself. -/
def id (m : Type u → Type v) [Monad m] : m →ᵐ m where
  toFun _ mx := mx
  toFun_pure' _ := by simp
  toFun_bind' _ _ := by simp

/-- Compose two `MonadHom`s together by applying them in sequence. -/
protected def comp (G : n →ᵐ n') (F : m →ᵐ n) : m →ᵐ n' where
  toFun _ := G.toFun _ ∘ F.toFun _
  toFun_pure' := by simp
  toFun_bind' := by simp

/-- Infix notation for composition of monad homomorphisms, `G ∘ᵐ F`. The superscript
matches the arrow `→ᵐ` and keeps the glyph distinct from Mathlib's `κ ∘ₘ μ`. -/
infixr:90 " ∘ᵐ " => MonadHom.comp

/-- `pure`/`return` lawfully embed the `Id` monad into any lawful monad. -/
protected def pure (m) [Monad m] [LawfulMonad m] : Id →ᵐ m where
  toFun _ mx := pure mx.run
  toFun_pure' x := by simp
  toFun_bind' mx my := by simp

end MonadHom

namespace StateT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {σ α : Type u}

variable {n' : Type u → Type x} [Monad n'] [LawfulMonad n']

end StateT

namespace ReaderT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {ρ α : Type u}

variable {n' : Type u → Type x} [Monad n'] [LawfulMonad n']

end ReaderT

namespace OptionT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {α : Type u}

variable {n' : Type u → Type x} [Monad n'] [LawfulMonad n']

end OptionT

namespace ExceptT

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n] {ε α : Type u}

variable {n' : Type u → Type x} [Monad n'] [LawfulMonad n']

end ExceptT
