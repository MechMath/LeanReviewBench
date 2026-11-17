module

public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Set.Functor
public import dep.PolyFun.Control.Monad.Support

@[expose] public section

universe u v w

namespace MonadAttach

variable {m : Type u → Type v} {α β : Type u}

section Transport

variable {m : Type u → Type v} {n : Type u → Type w} {α : Type u}

variable [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]

variable [Monad n] [LawfulMonad n] [MonadAttach n] [LawfulMonadAttach n]

variable [MonadLiftT m n] [LawfulMonadLiftT m n]

end Transport

section Instances

/-- Core's `MonadAttach (ExceptT ε m)` is stated at `max`-joined universes, which blocks
synthesis in a universe-polymorphic context; this alias instantiates it at a single
universe. Delete once the upstream declaration is repaired. -/
instance instMonadAttachExceptT {ε : Type u} {m : Type u → Type v} [Monad m]
    [MonadAttach m] : MonadAttach (ExceptT ε m) :=
  instMonadAttachExceptTOfMonad.{u, u, v}

/-- The powerset monad is its own support. -/
instance instMonadAttachSetM : MonadAttach SetM where
  CanReturn s a := a ∈ SetM.run s
  attach _ := (Set.univ : Set _)

instance instLawfulMonadAttachSetM : LawfulMonadAttach SetM := sorry

instance instExactMonadAttachId : ExactMonadAttach Id := sorry

instance instExactMonadAttachOption : ExactMonadAttach Option := sorry

instance instMonadAttachExcept434 {ε : Type u} : MonadAttach (Except ε) :=
  inferInstanceAs (MonadAttach (ExceptT ε Id))

instance instLawfulMonadAttachExcept434 {ε : Type u} : LawfulMonadAttach (Except ε) := sorry

instance instExactMonadAttachExcept {ε : Type u} : ExactMonadAttach (Except ε) := sorry

instance instExactMonadAttachSetM : ExactMonadAttach SetM := sorry

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

instance instExactMonadAttachOptionT : ExactMonadAttach (OptionT m) := sorry

instance instExactMonadAttachExceptT {ε : Type u} : ExactMonadAttach (ExceptT ε m) := sorry

section Unfoldings

variable {α : Type u}

variable {m : Type u → Type v} [Monad m] [MonadAttach m]

end Unfoldings

section WriterT

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m]

variable {ω : Type u} [Monoid ω]

instance instMonadAttachWriterT : MonadAttach (WriterT ω m) where
  CanReturn x a := ∃ w, CanReturn x.run (a, w)
  attach x := WriterT.mk <|
    (fun p => (⟨p.1.1, ⟨p.1.2, p.2⟩⟩, p.1.2)) <$> MonadAttach.attach x.run

instance instWeaklyLawfulMonadAttachWriterT [WeaklyLawfulMonadAttach m] :
    WeaklyLawfulMonadAttach (WriterT ω m) := sorry

instance instLawfulMonadAttachWriterT [LawfulMonadAttach m] :
    LawfulMonadAttach (WriterT ω m) := sorry

/-- Both introduction rules hold: `pure` writes the unit accumulator, and composable
outputs compose with their accumulators multiplied. This is what `StateT` cannot have —
there is no input index to quantify over, so nothing is flattened away. -/
instance instExactMonadAttachWriterT [ExactMonadAttach m] : ExactMonadAttach (WriterT ω m) := sorry

end WriterT

end Instances

end MonadAttach
