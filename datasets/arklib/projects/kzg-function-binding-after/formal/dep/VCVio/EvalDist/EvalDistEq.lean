module

public import Batteries.Tactic.Lint.Basic
public import Lean.PrettyPrinter.Delaborator.Basic
public import Lean.PrettyPrinter.Formatter
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.FunLike.IsApply
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.EMetricSpace.Weak
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import dep.ToMathlib.Data.Vector.Induction
public import dep.ToMathlib.MeasureTheory.Measure.Subprobability
public import dep.VCVio.EvalDist.Defs.Measure.Core
public import dep.VCVio.EvalDist.ProbabilityNotation
public import dep.VCVio.EvalDist.ProbabilityNotation.Attr

public section

open MeasureTheory

open scoped ENNReal

universe v v' v''

section defs

variable {m : Type → Type v} {m' : Type → Type v'} [EvalDistSemantics m] [EvalDistSemantics m']
  [Monad m] [Monad m'] {α : Type}

/-- Two computations are equal in distribution when every event has the same probability under
both. -/
def EvalDistEq (mx : m α) (my : m' α) : Prop :=
  ∀ p : α → Prop, Pr{let x ← mx}[p x] = Pr{let y ← my}[p y]

@[inherit_doc] infix:50 " =ᵈ " => EvalDistEq

end defs

namespace EvalDistEq

variable {m : Type → Type v} {m' : Type → Type v'} {m'' : Type → Type v''}
  [Monad m] [Monad m'] [Monad m''] [EvalDistSemantics m] [EvalDistSemantics m']
  [EvalDistSemantics m''] {α β : Type}

@[refl, simp]
theorem refl (mx : m α) : mx =ᵈ mx := sorry

protected theorem rfl {mx : m α} : mx =ᵈ mx := sorry

@[symm]
theorem symm {mx : m α} {my : m' α} (h : mx =ᵈ my) : my =ᵈ mx := sorry

theorem trans {mx : m α} {my : m' α} {mz : m'' α} (h₁ : mx =ᵈ my) (h₂ : my =ᵈ mz) :
    mx =ᵈ mz := sorry

instance : @Trans (m α) (m' α) (m'' α) EvalDistEq EvalDistEq EvalDistEq := ⟨trans⟩

instance : Std.Refl (α := m α) EvalDistEq := sorry

instance : Std.Symm (α := m α) EvalDistEq := sorry

instance : IsTrans (m α) EvalDistEq := sorry

/-- A common map preserves equality in distribution. -/
theorem map [LawfulMonad m] [LawfulMonad m'] {mx : m α} {my : m' α} (h : mx =ᵈ my) (f : α → β) :
    f <$> mx =ᵈ f <$> my := sorry

section lawful

variable [LawfulMonad m] [LawfulMonad m'] [LawfulEvalDistSemantics m]
  [LawfulEvalDistSemantics m']

/-- Binds of computations and continuations equal in distribution are equal in distribution. -/
theorem bind {mx : m α} {my : m' α} (h : mx =ᵈ my) {f : α → m β} {g : α → m' β}
    (hfg : ∀ a, f a =ᵈ g a) : mx >>= f =ᵈ my >>= g := sorry

end lawful

section sameMonad

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

end sameMonad

end EvalDistEq
