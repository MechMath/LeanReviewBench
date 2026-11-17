module

public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Functor
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances
public import dep.VCVio.EvalDist.Defs.Support

public section

universe u v

attribute [grind →] LawfulMonadAttach.eq_of_canReturn_pure

/-- Failure has no possible outputs under monadic attachment. -/
protected class HasEvalSet.LawfulFailure (m : Type u → Type v)
    [Alternative m] [MonadAttach m] : Prop where
  /-- Failure has empty attachment support. -/
  support_failure' {α : Type u} : support (failure : m α) = ∅

variable {m : Type u → Type v} [Alternative m] [MonadAttach m]
  [HasEvalSet.LawfulFailure m] {α : Type u}

/-- Optional failure has no possible outputs when attachment respects pure computations. -/
instance OptionT.instLawfulFailure (m : Type u → Type v) [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] : HasEvalSet.LawfulFailure (OptionT m) := sorry
