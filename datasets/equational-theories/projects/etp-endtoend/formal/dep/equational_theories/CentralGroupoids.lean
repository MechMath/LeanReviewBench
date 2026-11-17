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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
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
import dep.equational_theories.SmallMagmas

private def ofMatrix {n : Nat} [Inhabited (Fin n)]
  (table : Array (Array (Fin n))) (x y : Fin n) : Fin n :=
  table[x.val]![y.val]!

/-- A 3x3 helper magma, A21, which streamlines the full construction. -/
private def MagmaA21 : Magma (Fin 3) where
  op := memoFinOp (ofMatrix #[ #[0, 1, 2], #[0, 2, 1], #[0, 2, 1] ])

/-- We define Knuth's A2 here in terms of A21. -/
def MagmaA2 : Magma (Fin 3 × Fin 3) where
  op (p1 p2 : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  match p1, p2 with
  | (a, b), (⟨0, _⟩, _) => (MagmaA21.op a b, ⟨0, sorry⟩)
  | (_, b), (c, ⟨0, _⟩) => (b, MagmaA21.op b c)
  | (_, b), (c, _)     => (b, c)

/-- A magma isomorphic to A2, given as an optable. -/
def MagmaA2T : Magma (Fin 9) where
  op := memoFinOp (ofMatrix #[ #[0, 0, 0, 1, 1, 1, 2, 2, 2], #[3, 3, 3, 5, 4, 4, 4, 5, 5], #[6, 6, 6, 8, 7, 7, 7, 8, 8], #[0, 0, 0, 1, 1, 1, 2, 2, 2], #[6, 6, 6, 5, 4, 4, 4, 5, 5], #[3, 3, 3, 8, 7, 7, 7, 8, 8], #[0, 0, 0, 1, 1, 1, 2, 2, 2], #[6, 6, 6, 5, 4, 4, 4, 5, 5], #[3, 3, 3, 8, 7, 7, 7, 8, 8]])

local instance : Magma (Fin 3 × Fin 3) := MagmaA2

local instance : Magma (Fin 9) := MagmaA2T
