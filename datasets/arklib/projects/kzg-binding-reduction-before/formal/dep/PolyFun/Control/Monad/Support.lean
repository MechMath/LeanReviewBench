module

public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Set.Functor

@[expose] public section

universe u v w

/-- Exact pure and bind composition for the existing lawful attachment predicate.

The two introduction rules complement core's elimination rules to give support equations.
This class carries proofs only: `LawfulMonadAttach` already fixes the return predicate,
while these additional laws need not hold for every lawful monad. -/
class ExactMonadAttach (m : Type u → Type v) [Monad m] [MonadAttach m]
    extends LawfulMonadAttach m where
  /-- A pure computation can return its own value. -/
  canReturn_pure {α : Type u} (a : α) : MonadAttach.CanReturn (pure a : m α) a
  /-- Possible outputs compose along `bind`. -/
  canReturn_bind {α β : Type u} {x : m α} {f : α → m β} {a : α} {b : β} :
    MonadAttach.CanReturn x a → MonadAttach.CanReturn (f a) b →
      MonadAttach.CanReturn (x >>= f) b

namespace MonadAttach

variable {m : Type u → Type v} {α β : Type u}

/-- The set of possible outputs of a monadic computation: the `Set`-valued view of
`CanReturn`. Available for any `MonadAttach`; the structural equations are gated behind
`ExactMonadAttach`. -/
def support [MonadAttach m] (x : m α) : Set α :=
  {a | CanReturn x a}

section Laws

variable [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

end Laws

/-- Every possible output of `x` satisfies `p` — the "always true" judgment.

Stated over `CanReturn` rather than as a bounded quantifier over `support`, because the
modality does not need to expose a `Set` in its interface. This makes the same shape easy
to index when a flattened set of values is too coarse, as for `StateT`; the indexed
carrier there is still the honest set of value/final-state pairs. The two unindexed
spellings are definitionally interchangeable — `allOutputs_iff_forall_support` and
`allOutputs_iff_forall_canReturn` are both `Iff.rfl` — so nothing downstream has to choose. -/
def AllOutputs [MonadAttach m] (p : α → Prop) (x : m α) : Prop :=
  ∀ a, CanReturn x a → p a

/-- Some possible output of `x` satisfies `p`. The angelic half of the pair; see
`AllOutputs` for why it is stated over `CanReturn`. -/
def SomeOutput [MonadAttach m] (p : α → Prop) (x : m α) : Prop :=
  ∃ a, CanReturn x a ∧ p a

/-- No possible output of `x` satisfies `p` — the "never true" judgment. -/
def NoOutput [MonadAttach m] (p : α → Prop) (x : m α) : Prop :=
  AllOutputs (fun a => ¬ p a) x

@[inherit_doc AllOutputs]
scoped notation:50 x:51 " ⊨ₐ " p:51 => MonadAttach.AllOutputs p x

@[inherit_doc SomeOutput]
scoped notation:50 x:51 " ⊨ₛ " p:51 => MonadAttach.SomeOutput p x

@[inherit_doc NoOutput]
scoped notation:50 x:51 " ⊭ " p:51 => MonadAttach.NoOutput p x

section Judgments

variable [MonadAttach m]

end Judgments

section JudgmentLaws

variable [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

end JudgmentLaws

end MonadAttach
