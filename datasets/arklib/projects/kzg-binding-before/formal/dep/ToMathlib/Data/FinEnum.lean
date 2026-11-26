module

public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Sym
public import Mathlib.Logic.Embedding.Basic

@[expose] public section

universe u

/-- Completeness of `List.sym`: every `z : Sym α n` whose members all lie in `xs` is enumerated by
`xs.sym n`. This is the converse of `List.mem_of_mem_of_mem_sym`. -/
theorem List.mem_sym {α : Type u} :
    ∀ {n : ℕ} {xs : List α} {z : Sym α n}, (∀ a ∈ z, a ∈ xs) → z ∈ xs.sym n
  := sorry

/-- `Bool` enumerated as `[true, false]`. -/
instance : FinEnum Bool := .ofList [true, false] (sorry)

/-- Computable enumeration of size-`n` multisets over a `FinEnum` type, drawn from `List.sym` of
the canonical enumeration. Every `z : Sym α n` qualifies since all its members lie in
`FinEnum.toList`. -/
@[reducible] def Sym.finEnum {α : Type u} [FinEnum α] (n : ℕ) : FinEnum (Sym α n) :=
  FinEnum.ofNodupList ((FinEnum.toList α).sym n)
    (fun _ => List.mem_sym fun a _ => FinEnum.mem_toList a)
    (List.Nodup.sym n FinEnum.nodup_toList)

/-- Computable enumeration of permutations of a `FinEnum` type via `permsOfList` applied to the
canonical enumeration. Completeness holds because every element a permutation can move lies in
`FinEnum.toList`. -/
@[reducible] def Equiv.Perm.finEnum {α : Type u} [FinEnum α] : FinEnum (Equiv.Perm α) :=
  FinEnum.ofNodupList (permsOfList (FinEnum.toList α))
    (fun _ => mem_permsOfList_of_mem fun x _ => FinEnum.mem_toList x)
    (nodup_permsOfList FinEnum.nodup_toList)

/-- Computable enumeration of embeddings `β ↪ α` between `FinEnum` types, transported from the
`FinEnum` on the subtype of injective functions `{f : β → α // Function.Injective f}`. Injectivity
is decidable for functions out of a finite domain, so this subtype is itself `FinEnum`. -/
@[reducible] def Function.Embedding.finEnum {β α : Type u} [FinEnum β] [FinEnum α] :
    FinEnum (β ↪ α) :=
  FinEnum.ofEquiv { f : β → α // Function.Injective f }
    (Equiv.subtypeInjectiveEquivEmbedding β α).symm
