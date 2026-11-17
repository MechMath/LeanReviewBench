import Lean
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw

open FreeMagma

open Law

inductive FreeSemigroup (α : Type _)
  | Singleton : α → FreeSemigroup α
  | Cons : α → FreeSemigroup α → FreeSemigroup α

local postfix:61 ".+" => FreeSemigroup.Singleton

local infixr:60 " ,+ " => FreeSemigroup.Cons

def semigroupConcat {α : Type _} (s1 s2 : FreeSemigroup α) : FreeSemigroup α :=
  match s1 with
    | a .+        => a ,+ s2
    | a ,+ s1tail => a ,+ (semigroupConcat s1tail s2)

instance (α : Type _) : Magma (FreeSemigroup α) where
  op := semigroupConcat

def freeMagmaToFreeSgr {α : Type _} : MagmaHom (FreeMagma α) (FreeSemigroup α) where
  toFun := fun t ↦ evalInMagma FreeSemigroup.Singleton t
  map_op' := fun s _ ↦ match s with
    | Lf _ => rfl
    | _ ⋆ _ => rfl

local postfix:70 " ↠Sgr " => freeMagmaToFreeSgr.toFun
