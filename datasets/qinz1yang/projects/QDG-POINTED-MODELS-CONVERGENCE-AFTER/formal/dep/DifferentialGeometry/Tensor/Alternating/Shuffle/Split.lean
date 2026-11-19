




import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod

namespace DifferentialGeometry.ShuffleSplit

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {α₀ : Type*} {β : Type*}

def optionSumEquiv : Option α₀ ⊕ β ≃ Option (α₀ ⊕ β) where
  toFun := fun x => match x with
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  invFun := fun x => match x with
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  left_inv := by intro x; rcases x with ((_ | a) | b) <;> rfl
  right_inv := by intro x; rcases x with (_ | (a | b)) <;> rfl

@[simp] theorem optionSumEquiv_inl_none :
    optionSumEquiv (Sum.inl (none : Option α₀) : Option α₀ ⊕ β) = none  := by sorry

@[simp] theorem optionSumEquiv_inl_some (a : α₀) :
    optionSumEquiv (Sum.inl (some a) : Option α₀ ⊕ β) = some (Sum.inl a)  := by sorry

@[simp] theorem optionSumEquiv_inr (b : β) :
    optionSumEquiv (Sum.inr b : Option α₀ ⊕ β) = some (Sum.inr b)  := by sorry

@[simp] theorem optionSumEquiv_symm_none :
    optionSumEquiv.symm (none : Option (α₀ ⊕ β)) = Sum.inl none  := by sorry

@[simp] theorem optionSumEquiv_symm_some_inl (a : α₀) :
    optionSumEquiv.symm (some (Sum.inl a) : Option (α₀ ⊕ β)) =
      Sum.inl (some a)  := by sorry

@[simp] theorem optionSumEquiv_symm_some_inr (b : β) :
    optionSumEquiv.symm (some (Sum.inr b) : Option (α₀ ⊕ β)) = Sum.inr b  := by sorry

theorem preimage_inl_none_side_well_defined
    {σ : Equiv.Perm (Option α₀ ⊕ β)}
    (τ_l : Equiv.Perm (Option α₀)) (τ_r : Equiv.Perm β) :
    (∃ k, σ⁻¹ (Sum.inl none) = Sum.inl k) ↔
    (∃ k, (σ * Equiv.Perm.sumCongr τ_l τ_r)⁻¹ (Sum.inl none) = Sum.inl k)  := by sorry

theorem preimage_inl_none_side_well_defined_of_mem_range
    {σ : Equiv.Perm (Option α₀ ⊕ β)}
    (τ : (Equiv.Perm.sumCongrHom (Option α₀) β).range) :
    (∃ k, σ⁻¹ (Sum.inl none) = Sum.inl k) ↔
    (∃ k, (σ * ↑τ)⁻¹ (Sum.inl none) = Sum.inl k)  := by sorry

theorem optionCongr_removeNone_of_fix_none {α : Type*}
    (σ : Equiv.Perm (Option α)) (h : σ none = none) :
    (Equiv.removeNone σ).optionCongr = σ  := by sorry

theorem removeNone_inv_mul {α : Type*}
    (σ₁ σ₂ : Equiv.Perm (Option α))
    (h₁ : σ₁ none = none) (h₂ : σ₂ none = none) :
    Equiv.removeNone (σ₁⁻¹ * σ₂) =
      (Equiv.removeNone σ₁)⁻¹ * Equiv.removeNone σ₂  := by sorry

theorem removeNone_sign {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm (Option α)) (h : σ none = none) :
    Equiv.Perm.sign (Equiv.removeNone σ) = Equiv.Perm.sign σ  := by sorry

theorem permCongr_sign {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (e : α ≃ β) (σ : Equiv.Perm α) :
    Equiv.Perm.sign (Equiv.permCongr e σ) = Equiv.Perm.sign σ  := by sorry

theorem permCongr_inv_mul {α β : Type*}
    (e : α ≃ β) (σ₁ σ₂ : Equiv.Perm α) :
    Equiv.permCongr e (σ₁⁻¹ * σ₂) =
      (Equiv.permCongr e σ₁)⁻¹ * Equiv.permCongr e σ₂  := by sorry

end DifferentialGeometry.ShuffleSplit

