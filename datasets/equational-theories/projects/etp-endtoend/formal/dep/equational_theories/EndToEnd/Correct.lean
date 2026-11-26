import Batteries.Data.Array.Lemmas
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.ToExpr
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Cases
import dep.equational_theories.EndToEnd.Basic
import dep.equational_theories.EndToEnd.Certificate
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.Equations.LawsComplete
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.RArray

namespace EndToEnd

variable {C : Certificate} {pos : RArray PosFact} {neg : RArray NegFact} {i j c e : Nat}

/-- The facts `checkCert` establishes, in usable per-index form. -/
structure Valid (C : Certificate) (pos : RArray PosFact) (neg : RArray NegFact) : Prop where
  clsLt : ∀ e, e < C.numEq → C.scc.get e < C.numSccs
  scc : ∀ e, e < C.numEq → checkScc C pos e = true
  fmaskOk : ∀ k, k < C.numNeg → checkFmask C neg k = true
  fwd : ∀ i, i < C.numSccs → checkFwd C pos i = true
  rev : ∀ i, i < C.numSccs → checkRev C pos i = true
  refutersOk : ∀ i, i < C.numSccs → checkRefuters C neg i = true

end EndToEnd
