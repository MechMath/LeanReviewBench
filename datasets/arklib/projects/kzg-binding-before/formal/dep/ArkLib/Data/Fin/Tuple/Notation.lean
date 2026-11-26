module

public import Batteries.Data.Fin.Fold
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import dep.ArkLib.Data.Classes.Slice
public import dep.ArkLib.Data.Fin.Tuple.Defs
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

universe u v v' w

namespace Fin

instance {n : ℕ} {α : Fin n → Type*} : SliceLT ((i : Fin n) → α i) ℕ
    (fun _ stop => stop ≤ n)
    (fun _ stop h => (i : Fin stop) → α (i.castLE h))
    where
  sliceLT := fun v stop h => take stop h v

instance {n : ℕ} {α : Fin n → Type*} : SliceGE ((i : Fin n) → α i) ℕ
    (fun _ start => start ≤ n)
    (fun _ start h =>
      (i : Fin (n - start)) → α (Fin.cast (Nat.sub_add_cancel h) (i.addNat start)))
    where
  sliceGE := fun v start h => drop start h v

instance {n : ℕ} {α : Fin n → Type*} : Slice ((i : Fin n) → α i) ℕ ℕ
    (fun _ start stop => start ≤ stop ∧ stop ≤ n)
    (fun _ start stop h =>
      (i : Fin (stop - start)) →
        α (castLE h.2 (Fin.cast (Nat.sub_add_cancel h.1) (i.addNat start))))
    where
  slice := fun v start stop h => Fin.drop start h.1 (Fin.take stop h.2 v)

end Fin

section Examples

open Fin

variable {n : ℕ} (hn5 : 5 ≤ n) (hn10 : 10 ≤ n) (v : Fin n → ℕ)

variable {α : Fin n → Type*} (hv : (i : Fin n) → α i)

variable (w : Fin 20 → ℕ)

end Examples

namespace Fin

@[inherit_doc]
infixr:67 " ::ᵛ " => Fin.vcons

@[inherit_doc]
infixl:65 " :+ᵛ " => Fin.vconcat

/-- `::ᵛ⟨α⟩` notation for homogeneous cons with explicit element type. -/
syntax:67 term:68 " ::ᵛ⟨" term "⟩ " term:67 : term

/-- `:+ᵛ⟨α⟩` notation for homogeneous concat with explicit element type. -/
syntax:65 term:66 " :+ᵛ⟨" term "⟩ " term:65 : term

/-- `++ᵛ⟨α⟩` notation for homogeneous append with explicit element type. -/
syntax:65 term:66 " ++ᵛ⟨" term "⟩ " term:65 : term

macro_rules
  | `($a:term ::ᵛ⟨$α:term⟩ $v:term) => `(Fin.vcons (α := $α) $a $v)

macro_rules
  | `($v:term :+ᵛ⟨$α:term⟩ $a:term) => `(Fin.vconcat (α := $α) $v $a)

macro_rules
  | `($u:term ++ᵛ⟨$α:term⟩ $v:term) => `(Fin.vappend (α := $α) $u $v)

/-- `!v[...]` notation constructs a vector using our custom functions.
Uses `!v[...]` to distinguish from standard `![]`. -/
syntax (name := finVecNotation) "!v[" term,* "]" : term

/-- `!v⟨α⟩[...]` notation constructs a vector with explicit type ascription.
Uses angle brackets to specify the element type, then square brackets for values. -/
syntax (name := finVecNotationWithType) "!v⟨" term "⟩[" term,* "]" : term

macro_rules
  | `(!v[$term:term, $terms:term,*]) => `((Fin.vcons $term !v[$terms,*]))
  | `(!v[$term:term]) => `((Fin.vcons $term !v[]))
  | `(!v[]) => `(Fin.vempty)

macro_rules
  | `(!v⟨$α⟩[$term:term, $terms:term,*]) => `(Fin.vcons (α := $α) $term !v⟨$α⟩[$terms,*])
  | `(!v⟨$α⟩[$term:term]) => `(Fin.vcons (α := $α) $term !v⟨$α⟩[])
  | `(!v⟨$α⟩[]) => `((Fin.vempty : Fin 0 → $α))

@[inherit_doc]
infixr:67 " ::ʰ " => Fin.hcons

@[inherit_doc]
infixl:65 " :+ʰ " => Fin.hconcat

/-- `::ʰ⟨α; β⟩` notation for hcons with explicit type ascriptions -/
syntax:67 term:68 " ::ʰ⟨" term "; " term "⟩ " term:67 : term

/-- `:+ʰ⟨α; β⟩` notation for hconcat with explicit type ascriptions -/
syntax:65 term:66 " :+ʰ⟨" term "; " term "⟩ " term:65 : term

/-- Functorial cons with explicit functor but inferred type families: `::ʰ⦃F⦄`. -/
syntax:67 term:68 " ::ʰ⦃" term "⦄ " term:67 : term

/-- Functorial cons (unary) with explicit types: `::ʰ⦃F⦄⟨α; β⟩`. -/
syntax:67 term:68 " ::ʰ⦃" term "⦄⟨" term "; " term "⟩ " term:67 : term

/-- Functorial cons (binary) with explicit types: `::ʰ⦃F⦄⟨α₁; β₁⟩⟨α₂; β₂⟩`. -/
syntax:67 term:68 " ::ʰ⦃" term "⦄⟨" term "; " term "⟩⟨" term "; " term "⟩ " term:67 : term

@[inherit_doc]
infixr:67 " ::ᵈ " => Fin.dcons

@[inherit_doc]
infixl:65 " :+ᵈ " => Fin.dconcat

/-- `::ᵈ⟨motive⟩` notation for dcons with explicit motive specification -/
syntax:67 term:68 " ::ᵈ⟨" term "⟩ " term:67 : term

/-- `:+ᵈ⟨motive⟩` notation for dconcat with explicit motive specification -/
syntax:65 term:66 " :+ᵈ⟨" term "⟩ " term:65 : term

/-- `!h[...]` notation constructs a heterogeneous tuple using hcons.
For automatic type inference without explicit motive. -/
syntax (name := finHeterogeneousNotation) "!h[" term,* "]" : term

/-- `!h⟨α⟩[...]` notation constructs a heterogeneous tuple with explicit type vector ascription.
Uses angle brackets to specify the type vector, then square brackets for values. -/
syntax (name := finHeterogeneousNotationWithTypeVec) "!h⟨" term "⟩[" term,* "]" : term

/-- `!h⦃F⦄[...]` functorial heterogeneous tuple with explicit functor and implicit type vectors. -/
syntax (name := finFunctorialHeterogeneousNotationShorthand) "!h⦃" term "⦄[" term,* "]" : term

/-- `!d[...]` notation constructs a dependent tuple using our custom dependent functions.
Uses `!d[...]` for dependent tuples with explicit motives. -/
syntax (name := finDependentNotation) "!d[" term,* "]" : term

/-- `!d⟨motive⟩[...]` notation constructs a dependent tuple with explicit motive specification.
Uses angle brackets to specify the motive, then square brackets for values. -/
syntax (name := finDependentNotationWithmotive) "!d⟨" term "⟩[" term,* "]" : term

macro_rules
  | `(!h[$term:term, $terms:term,*]) => `(Fin.hcons $term !h[$terms,*])
  | `(!h[$term:term]) => `(Fin.hcons $term !h[])
  | `(!h[]) => `((Fin.dempty))

macro_rules
  | `(!h⟨$typeVec⟩[$term:term, $terms:term,*]) =>
      `(($term : $typeVec 0) ::ʰ !h⟨fun i => $typeVec (Fin.succ i)⟩[$terms,*])
  | `(!h⟨$typeVec⟩[$term:term]) => `(($term : $typeVec 0) ::ʰ !h⟨fun i => $typeVec (Fin.succ i)⟩[])
  | `(!h⟨$typeVec⟩[]) => `((Fin.dempty : (i : Fin 0) → $typeVec i))

/-- Unary functorial: `!h⦃F⦄⟨α⟩[...]` where `α : Fin n → Sort _`. -/
syntax (name := finFunctorialHeterogeneousNotation)
  "!h⦃" term "⦄⟨" term "⟩[" term,* "]" : term

/-- Binary functorial: `!h⦃F⦄⟨α₁⟩⟨α₂⟩[...]` where `α₁, α₂ : Fin n → Sort _`. -/
syntax (name := finFunctorialBinaryHeterogeneousNotation)
  "!h⦃" term "⦄⟨" term "⟩⟨" term "⟩[" term,* "]" : term

macro_rules
  | `(!h⦃$F⦄⟨$α:term⟩[$x:term, $xs:term,*]) =>
    `(Fin.fcons (F := $F) (α := $α 0) (β := fun i => $α (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α (Fin.succ i)⟩[$xs,*])
  | `(!h⦃$F⦄⟨$α:term⟩[$x:term]) =>
    `(Fin.fcons (F := $F) (α := $α 0) (β := fun i => $α (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α (Fin.succ i)⟩[])
  | `(!h⦃$F⦄⟨$α:term⟩[]) => `((Fin.dempty : (i : Fin 0) → $F ($α i)))

macro_rules
  | `(!h⦃$F⦄⟨$α₁:term⟩⟨$α₂:term⟩[$x:term, $xs:term,*]) =>
    `(Fin.fcons₂ (F := $F)
        (α₁ := $α₁ 0) (β₁ := fun i => $α₁ (Fin.succ i))
        (α₂ := $α₂ 0) (β₂ := fun i => $α₂ (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α₁ (Fin.succ i)⟩⟨fun i => $α₂ (Fin.succ i)⟩[$xs,*])
  | `(!h⦃$F⦄⟨$α₁:term⟩⟨$α₂:term⟩[$x:term]) =>
    `(Fin.fcons₂ (F := $F)
        (α₁ := $α₁ 0) (β₁ := fun i => $α₁ (Fin.succ i))
        (α₂ := $α₂ 0) (β₂ := fun i => $α₂ (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α₁ (Fin.succ i)⟩⟨fun i => $α₂ (Fin.succ i)⟩[])
  | `(!h⦃$F⦄⟨$α₁:term⟩⟨$α₂:term⟩[]) =>
    `((Fin.dempty : (i : Fin 0) → $F ($α₁ i) ($α₂ i)))

macro_rules
  | `(!h⦃$F⦄[$term:term, $terms:term,*]) => `(Fin.fcons (F := $F) $term !h⦃$F⦄[$terms,*])
  | `(!h⦃$F⦄[$term:term]) => `(Fin.fcons (F := $F) $term !h⦃$F⦄[])
  | `(!h⦃$F⦄[]) => `((Fin.dempty : (i : Fin 0) → $F (_ i)))

macro_rules
  | `(!d[$term:term, $terms:term,*]) => `(Fin.dcons $term !d[$terms,*])
  | `(!d[$term:term]) => `(Fin.dcons $term !d[])
  | `(!d[]) => `(Fin.dempty)

macro_rules
  | `(!d⟨$motive⟩[$term:term, $terms:term,*]) =>
      `((Fin.dcons (motive := $motive) $term !d⟨fun i => $motive (Fin.succ i)⟩[$terms,*]))
  | `(!d⟨$motive⟩[$term:term]) => `((Fin.dcons (motive := $motive) $term !d[]))
  | `(!d⟨$motive⟩[]) => `((Fin.dempty : (i : Fin 0) → $motive i))

macro_rules
  | `($a:term ::ᵈ⟨$motive:term⟩ $b:term) => `(Fin.dcons (motive := $motive) $a $b)

macro_rules
  | `($a:term :+ᵈ⟨$motive:term⟩ $b:term) => `(Fin.dconcat (motive := $motive) $a $b)

macro_rules
  | `($a:term ::ʰ⟨$α:term; $β:term⟩ $b:term) => `(Fin.hcons (α := $α) (β := $β) $a $b)

macro_rules
  | `($a:term ::ʰ⦃$F:term⦄ $b:term) => `(Fin.fcons (F := $F) $a $b)
  | `($a:term ::ʰ⦃$F:term⦄⟨$α:term; $β:term⟩ $b:term) =>
    `(Fin.fcons (F := $F) (α := $α) (β := $β) $a $b)
  | `($a:term ::ʰ⦃$F:term⦄⟨$α₁:term; $β₁:term⟩⟨$α₂:term; $β₂:term⟩ $b:term) =>
    `(Fin.fcons₂ (F := $F) (α₁ := $α₁) (β₁ := $β₁) (α₂ := $α₂) (β₂ := $β₂) $a $b)

macro_rules
  | `($a:term :+ʰ⟨$α:term; $β:term⟩ $b:term) => `(Fin.hconcat (α := $α) (β := $β) $a $b)

syntax:65 term:66 " :+ʰ⦃" term "⦄ " term:65 : term

syntax:65 term:66 " :+ʰ⦃" term "⦄⟨" term "; " term "⟩ " term:65 : term

syntax:65 term:66 " :+ʰ⦃" term "⦄⟨" term "; " term "⟩⟨" term "; " term "⟩ " term:65 : term

macro_rules
  | `($u:term :+ʰ⦃$F:term⦄ $a:term) => `(Fin.fconcat (F := $F) $u $a)
  | `($u:term :+ʰ⦃$F:term⦄⟨$α:term; $β:term⟩ $a:term) =>
    `(Fin.fconcat (F := $F) (α := $α) (β := $β) $u $a)
  | `($u:term :+ʰ⦃$F:term⦄⟨$α₁:term; $β₁:term⟩⟨$α₂:term; $β₂:term⟩ $a:term) =>
    `(Fin.fconcat₂ (F := $F) (α₁ := $α₁) (β₁ := $β₁) (α₂ := $α₂) (β₂ := $β₂) $u $a)

end Fin

/-- Homogeneous vector append notation `++ᵛ` -/
infixl:65 " ++ᵛ " => Fin.vappend

/-- Dependent append notation `++ᵈ` -/
infixl:65 " ++ᵈ " => Fin.dappend

/-- Heterogeneous append notation `++ʰ` -/
infixl:65 " ++ʰ " => Fin.happend

/-- Heterogeneous append with explicit type ascriptions: `++ʰ⟨α; β⟩` -/
syntax:65 term:66 " ++ʰ⟨" term "; " term "⟩ " term:65 : term

/-- Dependent append with explicit motive: `++ᵈ⟨motive⟩` -/
syntax:65 term:66 " ++ᵈ⟨" term "⟩ " term:65 : term

/-- Functorial heterogeneous append with explicit functor but inferred types: `++ʰ⦃F⦄`. -/
syntax:65 term:66 " ++ʰ⦃" term "⦄ " term:65 : term

/-- Functorial heterogeneous append with unary functor: `++ʰ⦃F⦄⟨α; β⟩` -/
syntax:65 term:66 " ++ʰ⦃" term "⦄⟨" term "; " term "⟩ " term:65 : term

/-- Functorial heterogeneous append with binary functor: `++ʰ⦃F⦄⟨α₁; β₁⟩⟨α₂; β₂⟩` -/
syntax:65 term:66 " ++ʰ⦃" term "⦄⟨" term "; " term "⟩⟨" term "; " term "⟩ " term:65 : term

macro_rules
  | `($a:term ++ᵈ⟨$motive:term⟩ $b:term) => `(Fin.dappend (motive := $motive) $a $b)

macro_rules
  | `($a:term ++ʰ⟨$α:term; $β:term⟩ $b:term) =>
  `(Fin.happend (α := fun i => $α) (β := fun i => $β) $a $b)

macro_rules
  | `($a:term ++ʰ⦃$F:term⦄ $b:term) => `(Fin.fappend (F := $F) $a $b)

macro_rules
  | `($a:term ++ʰ⦃$F:term⦄⟨$α:term; $β:term⟩ $b:term) =>
    `(Fin.fappend (F := $F) (α := $α) (β := $β) $a $b)

macro_rules
  | `($a:term ++ʰ⦃$F:term⦄⟨$α₁:term; $β₁:term⟩⟨$α₂:term; $β₂:term⟩ $b:term) =>
    `(Fin.fappend₂ (F := $F) (α₁ := $α₁) (β₁ := $β₁) (α₂ := $α₂) (β₂ := $β₂) $a $b)

section Examples

section FinVecConsTests

end FinVecConsTests

section FinVecConcatTests

end FinVecConcatTests

section FinTupleConsTests

end FinTupleConsTests

section FinTupleConcatTests

end FinTupleConcatTests

section FinDependentConsTests

end FinDependentConsTests

section FinDependentConcatTests

end FinDependentConcatTests

section MixedTests

end MixedTests

section NewNotationTests

section DependentVectorTests

end DependentVectorTests

end NewNotationTests

end Examples
