import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.Preorder

open FreeMagma

variable {α : Type _}

def FreeMagma.dual : FreeMagma α → FreeMagma α
  | .Leaf x => .Leaf x
  | .Fork w₁ w₂ => .Fork w₂.dual w₁.dual

def Op.{u} (G : Type u) : Type u := G

variable {G : Type*} [Magma G]

instance opMagma : Magma (Op G) where op x y := (y ◇ x : G)

namespace Law.MagmaLaw

def dual (l : MagmaLaw α) : MagmaLaw α := { lhs := l.lhs.dual, rhs := l.rhs.dual }

def IsDual {α} (Law1 Law2 : MagmaLaw α) := Law1.iff Law2.dual

theorem IsDual.symm {Law1 Law2 : MagmaLaw α} (H : IsDual Law1 Law2) : IsDual Law2 Law1 := sorry

end Law.MagmaLaw
