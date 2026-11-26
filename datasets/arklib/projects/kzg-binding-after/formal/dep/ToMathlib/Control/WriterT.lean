module

public import Batteries.Control.AlternativeMonad
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Order.Basic

@[expose] public section

universe u v w

/-- Typeclass for instances where `∅` is an identity for `++`. -/
class LawfulAppend (α : Type u)
    [EmptyCollection α] [Append α] where
  empty_append (x : α) : ∅ ++ x = x
  append_empty (x : α) : x ++ ∅ = x
  append_assoc (x y z : α) : x ++ (y ++ z) = x ++ y ++ z

namespace LawfulAppend

attribute [simp] LawfulAppend.empty_append LawfulAppend.append_empty

attribute [grind =] LawfulAppend.empty_append
  LawfulAppend.append_empty LawfulAppend.append_assoc

instance {M : Type u → Type v} {ω : Type u} [Monad M]
    [EmptyCollection ω] [Append ω] [LawfulAppend ω] [LawfulMonad M] :
    LawfulMonad (WriterT ω M) := sorry

instance (α : Type u) : LawfulAppend (List α) := sorry

end LawfulAppend

namespace WriterT.AppendWP

/-- Append associativity supplies the core law used by the writer interpretation. -/
scoped instance instAssociativeOfLawfulAppend {ω : Type u} [EmptyCollection ω] [Append ω]
    [LawfulAppend ω] : Std.Associative (α := ω) (· ++ ·) where
  assoc a b c := (LawfulAppend.append_assoc a b c).symm

/-- The empty append log is a two-sided identity for the writer interpretation. -/
scoped instance instLawfulIdentityOfLawfulAppend {ω : Type u} [EmptyCollection ω] [Append ω]
    [LawfulAppend ω] : Std.LawfulIdentity (α := ω) (· ++ ·) ∅ where
  left_id := LawfulAppend.empty_append
  right_id := LawfulAppend.append_empty

end WriterT.AppendWP

namespace WriterT

section basic

variable {m : Type u → Type v} [Monad m] {ω : Type u} {α β γ : Type u}

section monoid

variable [Monoid ω]

end monoid

section append

variable [EmptyCollection ω]

variable [Append ω]

end append

end basic

section fail

variable {m : Type u → Type v} [AlternativeMonad m] {ω : Type u} {α β γ : Type u}

/-- Try `x₁`, falling back to `x₂ ()` through the `orElse` of the underlying monad `m`; the log
is the one written by the branch whose result is returned. -/
@[always_inline, inline]
protected def orElse {α : Type u} (x₁ : WriterT ω m α)
    (x₂ : Unit → WriterT ω m α) : WriterT ω m α :=
  WriterT.mk (x₁.run <|> (x₂ ()).run)

/-- The failing computation, inherited from the underlying monad `m`. -/
@[always_inline, inline]
protected def failure {α : Type u} : WriterT ω m α := WriterT.mk failure

instance [Monoid ω] : AlternativeMonad (WriterT ω m) where
  failure := WriterT.failure
  orElse  := WriterT.orElse

instance [Monoid ω] [LawfulMonad m] : LawfulMonadLift m (WriterT ω m) := sorry

end fail

end WriterT

/-- Writer monad transformer with additive cost accumulation.
Defined as `WriterT (Multiplicative ω) M`, which uses `Monoid (Multiplicative ω)`
(derived from `AddMonoid ω`) so that `tell` accumulates via `+` with identity `0`.

The types `Multiplicative ω` and `ω` are definitionally equal (`Multiplicative` is a plain
`def`, not a `structure`), so no runtime wrapping occurs. -/
abbrev AddWriterT (ω : Type u) (M : Type u → Type v) := WriterT (Multiplicative ω) M

namespace AddWriterT

variable {ω : Type u} {M : Type u → Type v} [Monad M] {α : Type u}

/-- Forget the additive cost log and keep only the outputs of an `AddWriterT` computation. -/
def outputs (oa : AddWriterT ω M α) : M α :=
  Prod.fst <$> oa.run

/-- Observe only the accumulated additive cost of an `AddWriterT` computation. -/
def costs (oa : AddWriterT ω M α) : M ω :=
  (fun z => Multiplicative.toAdd z.2) <$> oa.run

section costPredicates

/-- `CostsAs oa f` means that the accumulated cost of `oa` is determined by its output via the
function `f`.

Concretely, whenever `oa` produces output `a`, the recorded cost is exactly `f a`. This is a
strong structural property: it can fail when the same output can be reached by different execution
paths carrying different costs. -/
def CostsAs (oa : AddWriterT ω M α) (f : α → ω) : Prop :=
  oa.costs = f <$> oa.outputs

/-- `HasCost oa w` means that every execution path of `oa` incurs the constant cost `w`. -/
def HasCost (oa : AddWriterT ω M α) (w : ω) : Prop :=
  oa.CostsAs (fun _ ↦ w)

/-- `OutputCostAtMost oa w` means that `oa` admits an output-indexed cost description bounded above
by the constant `w`.

Concretely, there is some function `f : α → ω` such that every execution producing output `a`
accumulates cost `f a`, and each such `f a` is at most `w`. This is stronger than a merely
pathwise upper bound when the same output can be reached with different costs. -/
def OutputCostAtMost [Preorder ω] (oa : AddWriterT ω M α) (w : ω) : Prop :=
  ∃ f : α → ω, oa.CostsAs f ∧ ∀ a, f a ≤ w

/-- `OutputCostAtLeast oa w` means that `oa` admits an output-indexed cost description bounded
below by the constant `w`.

As with [`AddWriterT.OutputCostAtMost`], this packages a cost function determined by the final
output, not just an arbitrary pathwise lower bound. -/
def OutputCostAtLeast [Preorder ω] (oa : AddWriterT ω M α) (w : ω) : Prop :=
  ∃ f : α → ω, oa.CostsAs f ∧ ∀ a, w ≤ f a

/-- `Cost[ oa ] = w` means that the `AddWriterT` computation `oa` incurs the same additive cost
`w` on every execution path.

This is notation for [`AddWriterT.HasCost`]. It is intended for theorem statements where the
constant-cost reading is more natural than the underlying output-indexed formulation
[`AddWriterT.CostsAs`]. -/
syntax:max "Cost[ " term " ]" " = " term:50 : term

macro_rules
  | `(Cost[ $oa ] = $w) => `(AddWriterT.HasCost $oa $w)

/-- `OutputCost[ oa ] ≤ w` means that `oa` admits an output-indexed additive-cost bound by `w`.

This is notation for [`AddWriterT.OutputCostAtMost`]. It is best used when cost is already known
to be determined by the final output, or when that stronger formulation is useful in a proof. -/
syntax:max "OutputCost[ " term " ]" " ≤ " term:50 : term

macro_rules
  | `(OutputCost[ $oa ] ≤ $w) => `(AddWriterT.OutputCostAtMost $oa $w)

/-- `OutputCost[ oa ] ≥ w` means that `oa` admits an output-indexed additive-cost lower bound by
`w`.

This is notation for [`AddWriterT.OutputCostAtLeast`]. As with [`OutputCost[ oa ] ≤ w`], it is
formulated in terms of an output-indexed cost witness rather than arbitrary execution paths. -/
syntax:max "OutputCost[ " term " ]" " ≥ " term:50 : term

macro_rules
  | `(OutputCost[ $oa ] ≥ $w) => `(AddWriterT.OutputCostAtLeast $oa $w)

end costPredicates

end AddWriterT
