import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.FactsSyntax
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MemoFinOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

/--
Just for notational convenience, a way to specify magmas by multiplication table.

The use of `memoFinOp` below ensures that the actual computation is done efficiently, no matter
how `op` is defined here.
-/
private def ofMatrix {n : Nat} [Inhabited (Fin n)]
  (table : Array (Array (Fin n))) (x y : Fin n) : Fin n :=
  table[x.val]![y.val]!

/-- Magma (Fintype) is a Fintype. -/
instance instMagmaFintype (T : Type*) [DecidableEq T] [Fintype T] : Fintype (Magma T) :=
  Fintype.ofEquiv (T → T → T) ⟨Magma.mk, fun m ↦ m.op, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Proving that the list of order 2 magmas is complete. -/
def MagmaIso {T : Type*} (G H : Magma T) : Prop := Nonempty (@MagmaEquiv _ _ G H)

theorem MagmaIso_Equivalence {T : Type*} : Equivalence (MagmaIso (T := T)) := sorry

def MagmaIsoSetoid (T : Type*) : Setoid (Magma T) where
  r := MagmaIso
  iseqv := MagmaIso_Equivalence

/-- The type of magmas up to isomorphism -/
def MagmaUpToIso (T : Type*) := Quotient (MagmaIsoSetoid T)

def MagmaUpToIso.mk {T : Type*} (M : Magma T) := Quotient.mk (MagmaIsoSetoid T) M

instance magmaIsoSetoidDecidable {T : Type*} [DecidableEq T] [Fintype T] :
    DecidableRel (MagmaIsoSetoid T) :=
  fun a b ↦
    let _ : Fintype (@MagmaEquiv T T a b) := Fintype.ofEquiv
        (Subtype (α := T ≃ T) _) {
          toFun := fun ⟨f,h⟩ ↦ @MagmaEquiv.mk _ _ a b f h
          invFun := fun f ↦ ⟨f, @MagmaEquiv.map_op' _ _ a b f⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    decidable_of_iff' _ (show _ ↔ @Exists (@MagmaEquiv T T a b) fun _ ↦ True from sorry)

instance (k : ℕ) : Fintype (MagmaUpToIso (Fin k)) :=
  @Quotient.fintype _ _ _ magmaIsoSetoidDecidable

unsafe instance (k : ℕ) : Repr (MagmaUpToIso (Fin k)) :=
  ⟨fun m _ ↦
    let m' := Quot.unquot m
    repr $ (List.finRange k).map $ fun x ↦ (List.finRange k).map (fun y ↦ m'.op x y)⟩
