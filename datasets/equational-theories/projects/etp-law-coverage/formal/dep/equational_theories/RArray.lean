import Lean.ToExpr

inductive RArray (α : Type) : Type  where
  | leaf : α → RArray α
  | branch : Nat → RArray α → RArray α → RArray α

variable {α : Type}

/-- The crucial operation, written with very little abstractional overhead -/
noncomputable def RArray.get (a : RArray α) (n : Nat) : α :=
  RArray.rec (fun x _ => x) (fun p _ _ l r n => (p.ble n).rec (l n) (r (n.sub p))) a n

def RArray.getImpl (a : RArray α) (n : Nat) : α :=
  match a with
  | .leaf x => x
  | .branch p l r => if n < p then l.getImpl n else r.getImpl (n - p)

@[csimp]
theorem RArray.get_eq_getImpl : @RArray.get = @RArray.getImpl := sorry

instance : GetElem (RArray α) Nat α (fun _ _ => True) where
  getElem a n _ := a.get n

def RArray.size : RArray α → Nat
  | leaf _ => 1
  | branch _ l r => l.size + r.size

def RArray.checkSize : RArray α → Option Nat
  | leaf _ => some 1
  | branch n l r =>
    l.checkSize.bind fun a =>
    r.checkSize.bind fun b =>
    bif n.beq a then some (a + b) else none

def RArray.WF : RArray α → Prop
  | leaf _ => True
  | branch n l r => n = l.size ∧ l.WF ∧ r.WF

instance (arr : RArray α) : Decidable arr.WF :=
  decidable_of_bool arr.checkSize.isSome <| sorry

def RArray.ofFn {n : Nat} (f : Fin n → α) (h : 0 < n) : RArray α :=
  go 0 n h (Nat.le_refl _)
where
  go (lb ub : Nat) (h1 : lb < ub) (h2 : ub ≤ n) : RArray α :=
    if h : lb + 1 = ub then
      .leaf (f ⟨lb, Nat.lt_of_lt_of_le h1 h2⟩)
    else
      let mid := (lb + ub)/2
      .branch (mid - lb) (go lb mid (sorry) (sorry)) (go mid ub (sorry) h2)

section Meta

open Lean

def RArray.toExpr (ty : Expr) (f : α → Expr) : _root_.RArray α → Expr
  | .leaf x       =>
    mkApp2 (mkConst ``RArray.leaf) ty (f x)
  | .branch p l r =>
    mkApp4 (mkConst ``RArray.branch) ty (.lit (.natVal p)) (l.toExpr ty f) (r.toExpr ty f)

instance [ToExpr α] : ToExpr (_root_.RArray α) where
  toExpr a := a.toExpr (toTypeExpr α) (toExpr ·)
  toTypeExpr := mkApp (mkConst ``_root_.RArray) (toTypeExpr α)

end Meta
