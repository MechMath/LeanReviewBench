import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.Magma

/-- `MagmaHom G H` is the type of functions `G → H` that preserve the operation. -/
structure MagmaHom (G H : Type*) [Magma G] [Magma H] where
  /-- The underlying function. -/
  toFun : G → H
  /-- The function preserves the operation. -/
  map_op' : ∀ x y : G, toFun (x ◇ y) = toFun x ◇ toFun y

infixr:25 " →◇ " => MagmaHom

instance MagmaHom.toFunLike {G H : Type*} [Magma G] [Magma H] : FunLike (G →◇ H) G H where
  coe := MagmaHom.toFun
  coe_injective _ _ := (mk.injEq ..).mpr

instance {G H : Type*} [Magma G] [Magma H] : CoeFun (G →◇ H) (fun _ ↦ G → H) where
  coe f := f

@[ext]
lemma MagmaHom.ext {G H : Type*} [Magma G] [Magma H] {f₁ f₂ : G →◇ H}
    (hf : ∀ x : G, f₁ x = f₂ x) :
    f₁ = f₂ := sorry

/-- The function preserves the operation. -/
lemma MagmaHom.map_op {G H : Type*} [Magma G] [Magma H] (f : G →◇ H) (x y : G) :
    f (x ◇ y) = f x ◇ f y := sorry

/-- `MagmaHomClass F G H` states that `F` is a type of operation-preserving homomorphisms. -/
class MagmaHomClass (F : Type*) (G H : outParam Type*) [Magma G] [Magma H] [FunLike F G H] :
    Prop where
  /-- Given function preserves the operation. -/
  map_op : ∀ f : F, ∀ x y : G, f (x ◇ y) = f x ◇ f y

instance MagmaHom.toMagmaHomClass {G H : Type*} [Magma G] [Magma H] :
    MagmaHomClass (G →◇ H) G H := sorry

def MagmaHomClass.toMagmaHom {F G H : Type*} [Magma G] [Magma H] [FunLike F G H]
    [MagmaHomClass F G H] (f : F) :
    G →◇ H where
  toFun := f
  map_op' := map_op f

instance {F G H : Type*} [Magma G] [Magma H] [FunLike F G H] [MagmaHomClass F G H] :
    CoeTC F (G →◇ H) :=
  ⟨MagmaHomClass.toMagmaHom⟩

/-- `MagmaEquiv G H` is the type of equivalences `G ≃ H` that preserve the operation.
We call them magma isomorphisms. -/
structure MagmaEquiv (G H : Type*) [Magma G] [Magma H] extends G ≃ H, MagmaHom G H

infixl:25 " ≃◇ " => MagmaEquiv

instance MagmaEquiv.toFunLike {G H : Type*} [Magma G] [Magma H] : FunLike (G ≃◇ H) G H where
  coe := (·.toFun)
  coe_injective _ _ := (mk.injEq ..).mpr ∘ Equiv.coe_inj.mp

instance {G H : Type*} [Magma G] [Magma H] : CoeFun (G ≃◇ H) (fun _ ↦ G → H) where
  coe e := e

@[ext]
lemma MagmaEquiv.ext {G H : Type*} [Magma G] [Magma H] {e₁ e₂ : G ≃◇ H}
    (hf : ∀ x : G, e₁ x = e₂ x) :
    e₁ = e₂ := sorry

/-- `MagmaEquivClass F G H` states that `F` is a type of operation-preserving isomorphisms. -/
class MagmaEquivClass (F : Type*) (G H : outParam Type*) [Magma G] [Magma H] [EquivLike F G H] :
    Prop where
  /-- Given function preserves the operation. -/
  map_op : ∀ f : F, ∀ x y : G, f (x ◇ y) = f x ◇ f y

def MagmaEquivClass.toMagmaEquiv {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H]
    [MagmaEquivClass F G H] (f : F) :
    G ≃◇ H where
  left_inv := EquivLike.coe_symm_apply_apply f
  right_inv := EquivLike.apply_coe_symm_apply f
  map_op' := map_op f
  toFun := f
  invFun := EquivLike.inv f

instance {F G H : Type*} [Magma G] [Magma H] [EquivLike F G H] [MagmaEquivClass F G H] :
    CoeTC F (G ≃◇ H) :=
  ⟨MagmaEquivClass.toMagmaEquiv⟩

instance MagmaEquiv.toEquivLike {G H : Type*} [Magma G] [Magma H] :
    EquivLike (G ≃◇ H) G H where
  coe := (↑)
  inv f := f.symm
  coe_injective' _ _ h _ := DFunLike.coe_injective' h
  left_inv _ := Equiv.symm_apply_apply _
  right_inv _ := Equiv.apply_symm_apply _

instance MagmaEquiv.toMagmaEquivClass {G H : Type*} [Magma G] [Magma H] :
    MagmaEquivClass (G ≃◇ H) G H := sorry

instance (priority := 100) instMagmaHomClass (F : Type*) {G H : Type*} [Magma G] [Magma H]
    [EquivLike F G H] [FGH : MagmaEquivClass F G H] :
    MagmaHomClass F G H := sorry

lemma MagmaEquiv.symm_map_op {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) (x y : H) :
    e.symm (x ◇ y) = e.symm x ◇ e.symm y := sorry

/-- Inverse magma isomorphism. -/
def MagmaEquiv.symm {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) : H ≃◇ G :=
  ⟨e.toEquiv.symm, e.symm_map_op⟩

lemma MagmaEquiv.symm_apply_apply {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) (x : G) :
    e.symm (e x) = x := sorry

lemma MagmaEquiv.apply_symm_apply {G H : Type*} [Magma G] [Magma H] (e : G ≃◇ H) (y : H) :
    e (e.symm y) = y := sorry
