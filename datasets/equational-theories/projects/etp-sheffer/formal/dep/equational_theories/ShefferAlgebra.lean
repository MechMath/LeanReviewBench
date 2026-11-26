import Mathlib.Order.BooleanAlgebra.Set
import dep.equational_theories.Magma

section ShefferLaws

class Stroke (α : Type*) where
  stroke : α → α → α

infix:80 " | " => Stroke.stroke

def prime {α} [Stroke α] (a : α) := a | a

postfix:max " ′ " => prime

class ShefferAlgebra (α : Type*) extends Stroke α where
-- We need to assume α is nonempty
elt : α
sh₁ : ∀ a : α, a′′ = a
sh₂ : ∀ a b : α, a | (b | b′) = a′
sh₃ : ∀ a b c : α, (a | (b | c))′ = (b′ | a) | (c′ | a)

variable {α : Type*}

variable [ShefferAlgebra α]

open ShefferAlgebra

instance : Min α where
  min a b := (a′ | b′)

lemma inf (a b : α) : a ⊓ b = (a′ | b′) := sorry

instance : Max α where
 max a b := (a | b)′

lemma sup (a b : α) : a ⊔ b = (a | b)′ := sorry

instance : Compl α where
  compl a := a′

def z : α := elt | elt′

def u : α := z′

lemma inv (a a' : α) : a ⊔ a' = u → a ⊓ a' = z → a' = aᶜ := sorry

instance ShefferLE : LE α := ⟨ λ a b ↦ a = b ⊓ a ⟩

lemma Sheffer.le_refl (a : α) : a ≤ a := sorry

lemma Sheffer.le_trans (a b c : α) : a ≤ b → b ≤ c → a ≤ c := sorry

lemma Sheffer.le_antisymm (a b : α) : a ≤ b → b ≤ a → a = b := sorry

instance ShefferToBooleanAlg : BooleanAlgebra α where
  sup := (. ⊔ .)
  le_refl := fun a ↦ Sheffer.le_refl a
  le_trans := fun a b c a_1 a_2 ↦ Sheffer.le_trans a b c a_1 a_2
  le_antisymm := Sheffer.le_antisymm
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
  inf := (. ⊓ .)
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry
  le_sup_inf := sorry
  top := u
  bot := z
  inf_compl_le_bot := sorry
  top_le_sup_compl := sorry
  le_top := sorry
  bot_le := sorry

end ShefferLaws

section BooleanToSheffer

variable {α : Type*}

variable [BooleanAlgebra α]

end BooleanToSheffer
