module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.DepRewrite

@[expose] public section

universe u v w

section Prelude

end Prelude

/-- `DCast` is a type class for custom cast operations on an indexed type family `β a`

We require the cast operation `dcast`, along with the property that `dcast` reduces to `id` under
reflexivity. -/
class DCast (α : Sort*) (β : α → Sort*) where
  dcast : ∀ {a a' : α}, a = a' → β a → β a'
  dcast_id : ∀ {a : α}, dcast (Eq.refl a) = id

export DCast (dcast dcast_id)

attribute [simp] dcast_id

section DCast

variable {α : Sort*} {β : α → Sort*} [DCast α β] {a a' a'' : α} {b : β a} {b' : β a'}

/-- The default instance for `DCast` -/
instance (priority := low) : DCast α β where
  dcast h := cast (congrArg β h)
  dcast_id := sorry

@[simp]
theorem dcast_eq : dcast (Eq.refl a) b = b := sorry

@[simp]
theorem dcast_trans (h : a = a') (h' : a' = a'') :
    dcast h' (dcast h b) = dcast (h.trans h') b := sorry

end DCast

/-- `DCast₂` is a type class for custom cast operations on a doubly-indexed type family `γ a b`,
  given an underlying dependent cast `DCast α β`

We require the cast operation `dcast₂`, along with the property that `dcast₂` reduces to `id` under
reflexivity. -/
class DCast₂ (α : Sort*) (β : α → Sort*) (γ : (a : α) → β a → Sort*) [DCast α β] where
  dcast₂ : ∀ {a a' : α} {b : β a} {b' : β a'},
    (ha : a = a') → (dcast ha b = b') → γ a b → γ a' b'
  dcast₂_id : ∀ {a : α} {b : β a}, dcast₂ (Eq.refl a) dcast_eq = (id : γ a b → γ a b)

export DCast₂ (dcast₂ dcast₂_id)

attribute [simp] dcast₂_id

section DCast₂

variable {α : Sort*} {β : α → Sort*} {γ : (a : α) → β a → Sort*} [DCast α β] [DCast₂ α β γ]
  {a a' a'' : α} {b : β a} {b' : β a'} {b'' : β a''} {c : γ a b} {c' : γ a' b'} {c'' : γ a'' b''}

/-- Default instance for `DCast₂` -/
instance (priority := low) : DCast₂ α β γ where
  dcast₂ ha hb c := by
    refine cast ?_ c
    cases ha; simp at hb; cases hb; rfl
  dcast₂_id := sorry

@[simp]
theorem dcast₂_eq : dcast₂ (Eq.refl a) dcast_eq c = c := sorry

instance instDCast₁₂ : DCast (β a) (γ a) where
  dcast hb c := dcast₂ (Eq.refl a) (sorry) c
  dcast_id := sorry

instance instDCastPSigma : DCast ((a : α) ×' β a) (fun a => γ a.1 a.2) where
  dcast hab c := dcast₂ (sorry) (sorry) c
  dcast_id := sorry

instance instDCastSigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    [DCast α β] [DCast₂ α β γ] : DCast ((a : α) × β a) (fun a => γ a.1 a.2) where
  dcast hab c := dcast₂ (sorry) (sorry) c
  dcast_id := sorry

instance instDCastForall : DCast α (fun a => ∀ b : β a, γ a b) where
  dcast ha f := fun b => dcast₂ ha ((dcast_trans ha.symm ha).trans dcast_eq) (f (dcast ha.symm b))
  dcast_id := sorry

end DCast₂

/-- `DCast₃` is a type class for custom cast operations on a triply-indexed type family `δ a b c`,
  given underlying dependent casts `DCast α β` and `DCast₂ α β γ`

We require the cast operation `dcast₃`, along with the property that `dcast₃` reduces to `id` under
reflexivity. -/
class DCast₃ (α : Sort*) (β : α → Sort*) (γ : (a : α) → β a → Sort*)
    (δ : (a : α) → (b : β a) → γ a b → Sort*) [DCast α β] [DCast₂ α β γ] where
  dcast₃ : ∀ {a a' : α} {b : β a} {b' : β a'} {c : γ a b} {c' : γ a' b'},
    (ha : a = a') → (hb : dcast ha b = b') → (hc : dcast₂ ha hb c = c') → δ a b c → δ a' b' c'
  dcast₃_id : ∀ {a : α} {b : β a} {c : γ a b},
    dcast₃ (Eq.refl a) dcast_eq dcast₂_eq = (id : δ a b c → δ a b c)

export DCast₃ (dcast₃ dcast₃_id)

attribute [simp] dcast₃_id

section DCast₃

variable {α : Sort*} {β : α → Sort*} {γ : (a : α) → β a → Sort*}
  {δ : (a : α) → (b : β a) → γ a b → Sort*}
  [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ]
  {a a' a'' : α} {b : β a} {b' : β a'} {b'' : β a''}
  {c : γ a b} {c' : γ a' b'} {c'' : γ a'' b''}
  {d : δ a b c} {d' : δ a' b' c'} {d'' : δ a'' b'' c''}

/-- Default instance for `DCast₃` -/
instance (priority := low) : DCast₃ α β γ δ where
  dcast₃ ha hb hc d := by
    refine cast ?_ d
    cases ha; simp at hb; cases hb; simp at hc; cases hc; rfl
  dcast₃_id := sorry

instance instDCast₂₃ {a : α} : DCast₂ (β a) (γ a) (δ a) where
  dcast₂ ha hb c := dcast₃ (Eq.refl a) (sorry) (sorry) c
  dcast₂_id := sorry

instance instDCast₁₃ {a : α} {b : β a} : DCast (γ a b) (δ a b) where
  dcast hc d := dcast₃ (Eq.refl a) dcast_eq (sorry) d
  dcast_id := sorry

instance instDCast₂PSigma : DCast₂ ((a : α) ×' β a) (fun a => γ a.1 a.2) (fun a => δ a.1 a.2)
    where
  dcast₂ ha hb c := dcast₃ (sorry) (sorry) (sorry) c
  dcast₂_id := sorry

instance instDCast₂Sigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    {δ : (a : α) → (b : β a) → γ a b → Type*}
    [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ] :
    DCast₂ ((a : α) × β a) (fun a => γ a.1 a.2) (fun a => δ a.1 a.2) where
  dcast₂ ha hb c := dcast₃ (sorry) (sorry) (sorry) c
  dcast₂_id := sorry

instance instDCast₂Forall :
    DCast₂ α (fun a => ∀ b : β a, γ a b) (fun a f => ∀ b : β a, δ a b (f b)) where
  dcast₂ ha hb c := fun b => dcast₃ ha (sorry)
    (sorry) (c (dcast ha.symm b))
  dcast₂_id := sorry

instance instDCastPSigmaPSigma :
    DCast ((a : α) ×' (b : β a) ×' γ a b) (fun a => δ a.1 a.2.1 a.2.2) where
  dcast hc d := dcast₃ (sorry) (sorry) (sorry) d
  dcast_id := sorry

instance instDCastSigmaSigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    {δ : (a : α) → (b : β a) → γ a b → Type*}
    [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ] :
    DCast ((a : α) × (b : β a) × γ a b) (fun a => δ a.1 a.2.1 a.2.2) where
  dcast hc d := dcast₃ (sorry) (sorry) (sorry) d
  dcast_id := sorry

instance instDCastForallForall :
    DCast α (fun a => ∀ b : β a, ∀ c : γ a b, δ a b c) where
  dcast ha d := fun b c => dcast₃ ha (sorry) (sorry)
    (d (dcast ha.symm b) (dcast₂ ha.symm rfl c))
  dcast_id := sorry

instance instDCastPSigmaForall :
    DCast ((a : α) ×' (β a)) (fun ab => ∀ c : γ ab.1 ab.2, δ ab.1 ab.2 c) where
  dcast hab d := fun c => dcast₃ (sorry) (sorry) (sorry)
    (d (dcast₂ (sorry) (sorry) c))
  dcast_id := sorry

instance instDCastSigmaForallForall {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    {δ : (a : α) → (b : β a) → γ a b → Type*}
    [DCast α β] [DCast₂ α β γ] [DCast₃ α β γ δ] :
    DCast ((a : α) × (β a)) (fun ab => ∀ c : γ ab.1 ab.2, δ ab.1 ab.2 c) where
  dcast hab d := fun c => dcast₃ (sorry) (sorry) (sorry)
    (d (dcast₂ (sorry) (sorry) c))
  dcast_id := sorry

end DCast₃

namespace Fin

/-- `Fin.cast` as a `DCast` (which should override the default instance). -/
instance instDCast : DCast Nat Fin where
  dcast h := Fin.cast h
  dcast_id := sorry

end Fin
