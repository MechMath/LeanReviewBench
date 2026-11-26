import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.FactsSyntax
import dep.equational_theories.FreeMagma
import dep.equational_theories.FreeSemigroup
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

namespace Subgraph

namespace Eq1689

abbrev f {G: Type*} [Magma G] (a b : G) : G := (a ◇ b) ◇ b

abbrev g {G: Type*} [Magma G] (a b : G) : G := a ◇ ((a ◇ b) ◇ b)

lemma lem_1 {G: Type*} [Magma G] (h: Equation1689 G) :
    ∀ a b c : G, a ◇ (f (f a b) c) = f a b := sorry

lemma lem_2 {G: Type*} [Magma G] (h: Equation1689 G) :
    ∀ a b c : G, a ◇ (g b c) = f a b := sorry

end Eq1689

inductive Th
  | t1 : Th
  | t2 : Th
  | t3 : Th

def add : Th → Th → Th
| Th.t1, Th.t1 => Th.t2
| Th.t1, Th.t2 => Th.t3
| Th.t1, Th.t3 => Th.t3
| Th.t2, Th.t1 => Th.t3
| Th.t2, Th.t2 => Th.t3
| Th.t2, Th.t3 => Th.t3
| Th.t3, _ => Th.t3

end Subgraph
