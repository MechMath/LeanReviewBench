import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma

universe u

universe v

inductive FreeMagma (α : Type u)
  | Leaf : α → FreeMagma α
  | Fork : FreeMagma α → FreeMagma α → FreeMagma α
  deriving DecidableEq

instance (α : Type u) [Inhabited α] : Inhabited (FreeMagma α) where
  default := .Leaf default

instance (α : Type u) : Magma (FreeMagma α) where
  op := FreeMagma.Fork

instance (α : Type u) : Coe α (FreeMagma α) where
  coe x := FreeMagma.Leaf x

instance {n : Nat} : OfNat (FreeMagma ℕ) n := ⟨FreeMagma.Leaf n⟩

open Lean in
def FreeMagma.toJson {α} [ToJson α] : FreeMagma α → Json
  | FreeMagma.Leaf x => .mkObj [("leaf", Lean.toJson x)]
  | FreeMagma.Fork x y => .mkObj [("left", toJson x), ("right", toJson y)]

open Lean in
instance {α} [ToJson α] : ToJson (FreeMagma α) where
  toJson := FreeMagma.toJson

def FreeMagma.toString {α} [ToString α] (outermost : Bool) : FreeMagma α → String
  | FreeMagma.Leaf x => s!"{x}"
  | FreeMagma.Fork x y =>
    let s := s!"{x.toString false} ◇ {y.toString false}"
    if outermost then s else s!"({s})"

instance {α} [ToString α] : ToString (FreeMagma α) where
  toString := FreeMagma.toString true

infixl:65 " ⋆ " => FreeMagma.Fork

notation "Lf" => FreeMagma.Leaf

instance FreeMagma.isMagma {α} : Magma (FreeMagma α) := ⟨ Fork ⟩

namespace FreeMagma

def evalInMagma {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α → G
  | Lf a => f a
  | lchild ⋆ rchild => evalInMagma f lchild ◇ evalInMagma f rchild

notation:63 t:63 " ⬝ " σ:64 => evalInMagma σ t

def evalHom {α : Type u} {G : Type v} [Magma G] (f : α → G) : FreeMagma α →◇ G where
   toFun := evalInMagma f
   map_op' := fun _ _ ↦ rfl

def fmapHom {α : Type u} {β : Type v} (f : α → β) : FreeMagma α →◇ FreeMagma β :=
   evalHom (Lf ∘ f)

def Mem {α} (a : α) : FreeMagma α → Prop
  | Lf a' => a = a'
  | lchild ⋆ rchild => Mem a lchild ∨ Mem a rchild

def forks {α} : FreeMagma α → Nat
  | .Leaf _ => 0
  | .Fork m1 m2 => (m1.forks + m2.forks).succ

@[simp] def length {α} : FreeMagma α → Nat
  | .Leaf _ => 1
  | .Fork m1 m2 => FreeMagma.length m1 + FreeMagma.length m2

@[simp] def toList {α} : FreeMagma α → List α
  | Lf a => [a]
  | l ⋆ r => l.toList ++ r.toList

private def toListTR {α} : FreeMagma α → List α := go [] where
  go : List α → FreeMagma α → List α
  | acc, Lf a => a :: acc
  | acc, l ⋆ r => go (go acc r) l

@[csimp] private theorem toList_eq_toListTR : @toList = @toListTR := sorry

def elems {α} [DecidableEq α] : (m : FreeMagma α) → {l : List α // l.Nodup ∧ ∀ a, a ∈ l ↔ Mem a m}
  | Lf a => ⟨[a], List.nodup_singleton _, by simp [Mem]⟩
  | lchild ⋆ rchild => by
    let ⟨l, _, hl⟩ := lchild.elems
    let ⟨r, nr, hr⟩ := rchild.elems
    use l ∪ r, .union _ nr; simp [Mem, hl, hr]

end FreeMagma
