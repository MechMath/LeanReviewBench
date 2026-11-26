module

public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Functor
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances

@[expose] public section

universe u v w

variable {m : Type u → Type v} {α β γ : Type u}

section support

export MonadAttach (support)

/-- The monad `m` can be evaluated to get a finite set of possible outputs.
We restrict to the case of decidable equality of the output type, so `Finset.biUnion` exists.
Note: we can't use `MonadHomClass` since `Finset` has no `Monad` instance. -/
class HasEvalFinset (m : Type u → Type v) [MonadAttach m] where
  /-- The finite set of possible outputs of `mx`, whose coercion to a set is `support mx`. -/
  finSupport {α : Type u} [DecidableEq α] (mx : m α) : Finset α
  coe_finSupport {α : Type u} [DecidableEq α] (mx : m α) :
    (↑(finSupport mx) : Set α) = support mx

export HasEvalFinset (finSupport coe_finSupport)

attribute [simp, grind =] coe_finSupport

@[grind =, aesop unsafe norm]
lemma mem_finSupport_iff_mem_support [MonadAttach m] [HasEvalFinset m] [DecidableEq α]
    (mx : m α) (x : α) : x ∈ finSupport mx ↔ x ∈ support mx := sorry

end support

section forall_support

variable {m : Type u → Type v} [MonadAttach m] {α : Type u}

end forall_support

variable (p : Prop) [Decidable p]

section decidable

/-- Membership in the support of computations in. -/
protected class HasEvalSet.Decidable (m : Type u → Type v) [MonadAttach m] where
  /-- A decision procedure for whether a value is a possible output of `mx`. -/
  mem_support_decidable {α : Type u} (mx : m α) : DecidablePred (· ∈ support mx)

instance decidablePred_mem_support [MonadAttach m] [HasEvalSet.Decidable m]
    (mx : m α) : DecidablePred (· ∈ support mx) :=
  HasEvalSet.Decidable.mem_support_decidable mx

instance decidablePred_mem_finSupport [MonadAttach m] [HasEvalSet.Decidable m] [HasEvalFinset m]
    [DecidableEq α] (mx : m α) : DecidablePred (· ∈ finSupport mx) := by
  simpa only [mem_finSupport_iff_mem_support] using decidablePred_mem_support mx

end decidable
