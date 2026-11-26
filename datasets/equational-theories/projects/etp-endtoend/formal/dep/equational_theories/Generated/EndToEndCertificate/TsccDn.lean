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
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Cases
import dep.equational_theories.EndToEnd.Basic
import dep.equational_theories.EndToEnd.Certificate
import dep.equational_theories.EndToEnd.Dual
import dep.equational_theories.EndToEnd.Load
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
import dep.equational_theories.Generated.EndToEndCertificate.TsccDn0
import dep.equational_theories.Generated.EndToEndCertificate.TsccDn1
import dep.equational_theories.Generated.EndToEndCertificate.TsccDn2
import dep.equational_theories.Generated.EndToEndCertificate.TsccDn3
import dep.equational_theories.Generated.EndToEndCertificate.TsccDn4
import dep.equational_theories.Generated.EndToEndCertificate.TsccDn5
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MagmaOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.RArray

namespace EndToEnd

/-- 4694 entries, assembled from 6 shards. -/
def tsccdn : RArray (List Nat) :=
  (.branch 2403 (.branch 993 tsccdn0 (.branch 784 tsccdn1 tsccdn2)) (.branch 572 tsccdn3 (.branch 1665 tsccdn4 tsccdn5)))

end EndToEnd
