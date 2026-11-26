import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.Finset.Union
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Finset
import Mathlib.Order.Preorder.Chain
import Mathlib.Tactic.Group
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.FreeMagma
import dep.equational_theories.FreshGenerator
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

set_option backward.isDefEq.respectTransparency false

set_option backward.whnf.reducibleClassField false

namespace Eq1323

noncomputable section

section Ingredients

open symmDiff

variable {α : Type}

def FreeAbGrpExp2 (α : Type) : Type := Finset α

def FreeAbGrpExp2.mk : Finset α → FreeAbGrpExp2 α := id

def FreeAbGrpExp2.of (x : α) : FreeAbGrpExp2 α := FreeAbGrpExp2.mk {x}

def FreeAbGrpExp2.coords : FreeAbGrpExp2 α → Finset α := id

instance [DecidableEq α] : DecidableEq (FreeAbGrpExp2 α) := inferInstanceAs (DecidableEq (Finset α))

instance [Countable α] : Countable (FreeAbGrpExp2 α) := sorry

instance [Infinite α] : Infinite (FreeAbGrpExp2 α) := sorry

instance [DecidableEq α] : Add (FreeAbGrpExp2 α) where
  add a b := FreeAbGrpExp2.mk (a.coords ∆ b.coords)

instance : Zero (FreeAbGrpExp2 α) where zero := ⟨∅, sorry⟩

instance : Neg (FreeAbGrpExp2 α) where neg := id

theorem FreeAbGrpExp2.of_nonzero (x : α) : FreeAbGrpExp2.of x ≠ 0 := sorry

instance [DecidableEq α] : AddCommGroup (FreeAbGrpExp2 α) where
  add_zero x := sorry
  zero_add := sorry
  add_comm := sorry
  add_assoc := sorry
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := sorry

abbrev S := FreeAbGrpExp2 Nat

abbrev S' := {g : S // g ≠ 0}

instance : Infinite S' := sorry

inductive Sign where | plus | minus deriving DecidableEq

instance : Countable Sign := sorry

instance : Mul Sign where mul
  | .plus, .plus | .minus, .minus => .plus | .plus, .minus | .minus, .plus => .minus

instance : One Sign where one := .plus

instance : Inv Sign where inv := id

instance : Div Sign where div a b := a * b⁻¹

theorem Sign.div_eq_mul_inv (a b : Sign) : a / b = a * b := sorry

instance : CommGroup Sign where
  mul_one a := sorry
  one_mul a := sorry
  mul_comm a b := sorry
  mul_assoc a b c := sorry
  inv_mul_cancel a := sorry
  div_eq_mul_inv := Sign.div_eq_mul_inv

abbrev A₀ := FreeGroup Nat

@[reducible] def A := Sign × A₀ deriving DecidableEq

instance : Countable A := sorry

instance : Group A := inferInstanceAs (Group (Sign × A₀))

instance : Neg A where neg x := ⟨.minus, 1⟩ * x

@[simp] theorem A.neg {x : A} : -x = ⟨.minus, 1⟩ * x := sorry

abbrev R := A × S'

inductive Mod3 (n : ℕ) : Prop
  | rem0 : (k : ℕ) → n = 3 * k → Mod3 n
  | rem1 : (k : ℕ) → n = 3 * k + 1 → Mod3 n
  | rem2 : (k : ℕ) → n = 3 * k + 2 → Mod3 n

theorem Mod3.of (n : ℕ) : Mod3 n := sorry

end Ingredients

section Phi

instance : Denumerable S := Denumerable.finset

def iS : S ≃ ℕ := Denumerable.eqv S

def translationReprs (a : S') := { x | iS x < iS (x + a) }

def reprOf (a : S') (b : S) : Sign × translationReprs a :=
  if h : iS b < iS (b + a)
  then ⟨.plus, b, h⟩
  else
    let h : b + a ∈ translationReprs a := sorry
    ⟨.minus, b + a, h⟩

instance {a : S'} : Infinite (translationReprs a) := sorry

def ϕ₀ (a : S') : translationReprs a ≃ A₀ := nonempty_equiv_of_countable.some

def ϕ_offset (a : S') := (ϕ₀ a).invFun 1

def ϕ (a : S') (b : S) : A :=
  let ⟨sign, repr⟩ := reprOf a (b + ϕ_offset a)
  ⟨sign, ϕ₀ a repr⟩

@[simp] abbrev ϕ' (a : S') (b : S) : A₀ := (ϕ a b).2

def invϕ (a : S') (x : A) : S :=
  let b₀ : S := (ϕ₀ a).invFun x.2 + ϕ_offset a
  match x.1 with
  | .plus => b₀
  | .minus => b₀ + a

end Phi

section Relations

structure Relation where
  x : R
  y : R
  z : R
  nonDiag : x.2 ≠ y.2 ∧ y.2 ≠ z.2 ∧ z.2 ≠ x.2
deriving DecidableEq

structure RelationLHS where
  x : R
  y : R
  nonDiag : x.2 ≠ y.2

def RelationLHS.toPair (p : RelationLHS) := (p.x, p.y)

theorem RelationLHS.toPair.inj : Function.Injective RelationLHS.toPair
  := sorry

instance : Countable RelationLHS := sorry

variable {rel rel' : Relation}

variable {n m : ℕ}

def Relation.lhs : RelationLHS := ⟨rel.x, rel.y, rel.nonDiag.1⟩

def isFunc (A : Set Relation) : Prop :=
  ∀ {rel rel' : Relation}, rel ∈ A → rel' ∈ A → rel.lhs = rel'.lhs → rel.z = rel'.z

@[simp] def Relation.next (rel : Relation) : Relation :=
  ⟨rel.y, rel.z, ⟨rel.x.1 * ϕ rel.x.2 rel.y.2, rel.x.2⟩, sorry⟩

def Relation.skip : ℕ → Relation → Relation := Nat.repeat Relation.next

def Relation.orbit : Set Relation := { rel.skip n | n : ℕ }

abbrev Relation.squares : Finset S' := {rel.x.2, rel.y.2, rel.z.2}

def closure (F : Finset Relation) : Set Relation := { rel' | ∃ rel ∈ F, rel' ∈ rel.orbit }

def definedAt (F : Set Relation) (p : RelationLHS) : Prop := ∃ rel ∈ F, rel.lhs = p

end Relations

section Greedy

class Extension where
  core : Finset Relation
  func : isFunc (closure core)
  p : RelationLHS
  not_def : ¬definedAt (closure core) p

namespace Extension

variable [Extension]

def oldSquares : Finset S' := {p.x.2, p.y.2} ∪ core.biUnion fun a => a.squares

def old : Finset A₀ :=
  let fromValues := {p.x.1.2, p.y.1.2} ∪ core.biUnion fun a => {a.x.1.2, a.y.1.2, a.z.1.2}
  let fromPhis := (oldSquares ×ˢ oldSquares).image fun (x, y) => ϕ' x y
  fromValues ∪ fromPhis

abbrev freshA : A := ⟨.plus, FreeGroup.of <| FreshGenerator.freshGeneratorName old⟩

abbrev w : R := ⟨1, ⟨invϕ p.y.2 freshA, sorry⟩⟩

def newRelation : Relation := .mk p.x p.y w <| sorry

def next : Finset Relation := core ∪ {newRelation}

end Extension

def PartialSolution := { core : Finset Relation | isFunc (closure core) }

theorem extend (S : PartialSolution) (p : RelationLHS) (not_def : ¬definedAt (closure S.val) p)
    : ∃ S', S ≤ S' ∧ definedAt (closure S'.val) p := sorry

end Greedy

inductive G where
  | square : S → G
  | root : R → G
deriving DecidableEq

def op (f : RelationLHS → R) : G → G → G
  | .square a, .square b => .square (a + b)
  | .root x, .square b => .root (x.1 * ϕ x.2 b, x.2)
  | .square b, .root x => .root (x.1 * (ϕ x.2 b)⁻¹, x.2)
  | .root x, .root y =>
    if h : x.2 = y.2
      then .square (x.2 + invϕ x.2 (y.1⁻¹ * x.1))
      else .root (f ⟨x, y, h⟩)

def a : S' := ⟨FreeAbGrpExp2.of 1, FreeAbGrpExp2.of_nonzero _⟩

def b : S' := ⟨FreeAbGrpExp2.of 2, FreeAbGrpExp2.of_nonzero _⟩

def c : S' := ⟨FreeAbGrpExp2.of 4, FreeAbGrpExp2.of_nonzero _⟩

end

end Eq1323
