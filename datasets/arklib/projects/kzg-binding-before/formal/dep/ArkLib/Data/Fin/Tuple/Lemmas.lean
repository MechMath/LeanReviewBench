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
public import dep.ArkLib.Data.Fin.Tuple.Notation
public import dep.CompPoly.Data.Classes.DCast

@[expose] public section

universe u v w

namespace Fin

variable {m n : ℕ} {α : Sort u}

instance : Unique (Fin 0 → α) where
  uniq v := sorry

instance {α : Fin 0 → Sort u} : Unique ((i : Fin 0) → α i) where
  uniq := fun v => sorry

/-- `dcons` is equal to `cons`. Marked as `csimp` to allow for switching to the `cons`
  implementation during execution. -/
@[csimp]
theorem dcons_eq_cons : @dcons = @cons := sorry

@[simp]
theorem vconcat_last (v : Fin n → α) (a : α) : vconcat v a (Fin.last n) = a := sorry

@[simp]
theorem vconcat_castSucc (v : Fin n → α) (a : α) (i : Fin n) :
    vconcat v a (castSucc i) = v i := sorry

/-- `dconcat` is equal to `snoc`. Marked as `csimp` to allow for switching to the `snoc`
  implementation during execution. -/
@[csimp]
theorem dconcat_eq_snoc : @dconcat = @snoc := sorry

/-- Compiler implementation of `vconcat` using `snoc`. -/
def vconcatSnoc {α : Sort u} {n : ℕ} (v : Fin n → α) (a : α) : Fin (n + 1) → α :=
  snoc v a

/-- Compile `vconcat` using `vconcatSnoc`. -/
@[csimp]
theorem vconcat_eq_vconcatSnoc : @vconcat = @vconcatSnoc := sorry

/-- `dappend` is equal to `addCases`. Marked as `csimp` to allow for switching to the `addCases`
  implementation during execution. -/
@[csimp]
theorem dappend_eq_addCases : @dappend = @addCases := sorry

/-- `vappend` is equal to `append`. Marked as `csimp` to allow for switching to the `append`
  implementation during execution. -/
@[csimp]
theorem vappend_eq_append : @vappend = @append := sorry

@[simp]
theorem vappend_left (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    vappend u v (castAdd n i) = u i := sorry

@[simp]
theorem vappend_right (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    vappend u v (natAdd m i) = v i := sorry

section FunctorialBinary

variable {A : Sort u} {B : Sort v} {F₂ : A → B → Sort w} {m n : ℕ}

/-- Compiler implementation of `fconcat₂` using `snoc`. -/
def fconcat₂Snoc {A : Sort u} {B : Sort v} {F : A → B → Sort w} {n : ℕ}
    {α₁ : Fin n → A} {β₁ : A} {α₂ : Fin n → B} {β₂ : B}
    (u : (i : Fin n) → F (α₁ i) (α₂ i)) (a : F β₁ β₂) :
    (i : Fin (n + 1)) → F (vconcat α₁ β₁ i) (vconcat α₂ β₂ i) :=
  snoc (α := fun i => F (vconcat α₁ β₁ i) (vconcat α₂ β₂ i))
    (fun i => cast (congrArg₂ F (vconcat_castSucc α₁ β₁ i) (vconcat_castSucc α₂ β₂ i)).symm (u i))
    (cast (congrArg₂ F (vconcat_last α₁ β₁) (vconcat_last α₂ β₂)).symm a)

/-- Compile `fconcat₂` using `fconcat₂Snoc`. -/
@[csimp]
theorem fconcat₂_eq_fconcat₂Snoc : @fconcat₂ = @fconcat₂Snoc := sorry

/-- Compiler implementation of `fappend₂` using `addCases`. -/
def fappend₂AddCases {A : Sort u} {B : Sort v} {F : A → B → Sort w} {m n : ℕ}
    {α₁ : Fin m → A} {β₁ : Fin n → A} {α₂ : Fin m → B} {β₂ : Fin n → B}
    (u : (i : Fin m) → F (α₁ i) (α₂ i)) (v : (i : Fin n) → F (β₁ i) (β₂ i)) :
    (i : Fin (m + n)) → F (vappend α₁ β₁ i) (vappend α₂ β₂ i) :=
  addCases (motive := fun i => F (vappend α₁ β₁ i) (vappend α₂ β₂ i))
    (fun i => cast (congrArg₂ F (vappend_left α₁ β₁ i) (vappend_left α₂ β₂ i)).symm (u i))
    (fun i => cast (congrArg₂ F (vappend_right α₁ β₁ i) (vappend_right α₂ β₂ i)).symm (v i))

/-- Compile `fappend₂` using `fappend₂AddCases`. -/
@[csimp]
theorem fappend₂_eq_fappend₂AddCases : @fappend₂ = @fappend₂AddCases := sorry

end FunctorialBinary

section FunctorialUnary

variable {A : Sort u} {F : A → Sort v} {m n : ℕ} {α : A}

/-- Compiler implementation of `fconcat` using `snoc`. -/
def fconcatSnoc {A : Sort u} {F : A → Sort v} {n : ℕ} {α : Fin n → A} {β : A}
    (u : (i : Fin n) → F (α i)) (a : F β) : (i : Fin (n + 1)) → F (vconcat α β i) :=
  snoc (α := fun i => F (vconcat α β i))
    (fun i => cast (congrArg F (vconcat_castSucc α β i)).symm (u i))
    (cast (congrArg F (vconcat_last α β)).symm a)

/-- Compile `fconcat` using `fconcatSnoc`. -/
@[csimp]
theorem fconcat_eq_fconcatSnoc : @fconcat = @fconcatSnoc := sorry

/-- Compiler implementation of `fappend` using `addCases`. -/
def fappendAddCases {A : Sort u} {F : A → Sort v} {m n : ℕ} {α : Fin m → A} {β : Fin n → A}
    (u : (i : Fin m) → F (α i)) (v : (i : Fin n) → F (β i)) :
    (i : Fin (m + n)) → F (vappend α β i) :=
  addCases (motive := fun i => F (vappend α β i))
    (fun i => cast (congrArg F (vappend_left α β i)).symm (u i))
    (fun i => cast (congrArg F (vappend_right α β i)).symm (v i))

/-- Compile `fappend` using `fappendAddCases`. -/
@[csimp]
theorem fappend_eq_fappendAddCases : @fappend = @fappendAddCases := sorry

end FunctorialUnary

/-- Compiler implementation of `hconcat` using `snoc`. -/
def hconcatSnoc {n : ℕ} {α : Fin n → Sort u} {β : Sort u} (u : (i : Fin n) → α i) (a : β) :
    (i : Fin (n + 1)) → vconcat α β i :=
  fconcatSnoc (F := id) u a

/-- Compile `hconcat` using `hconcatSnoc`. -/
@[csimp]
theorem hconcat_eq_hconcatSnoc : @hconcat = @hconcatSnoc := sorry

/-- Compiler implementation of `happend` using `addCases`. -/
def happendAddCases {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) : (i : Fin (m + n)) → vappend α β i :=
  fappendAddCases (F := id) u v

/-- Compile `happend` using `happendAddCases`. -/
@[csimp]
theorem happend_eq_happendAddCases : @happend = @happendAddCases := sorry

instance {α : Fin 0 → Sort u} : Unique ((i : Fin 0) → α i) where
  default := fun i => elim0 i
  uniq v := sorry

variable {m n : ℕ} {α : Sort u}

section padding

end padding

end Fin
