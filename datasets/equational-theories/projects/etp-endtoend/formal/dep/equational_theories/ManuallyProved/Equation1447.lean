import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Topology.Instances.AddCircle.Real
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
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

namespace Equation1447

section Construction

universe u

variable {M : Type u} (S : M → M)

def no_fixed_points : Prop := ∀ (m : M), S m ≠ m ∧ S (S m) ≠ m ∧ S (S (S m)) ≠ m

variable (hnofix : no_fixed_points S)

include hnofix

def square_roots (x : M) : Set M := { y : M | S y = x }

notation "√" => square_roots

def parent (x : M) (y : M) : Prop := y = S x

variable  [DecidableEq M]

variable (arbitraryRoot : M → M)

variable (arbitraryRoot_root : ∀ (x : M), arbitraryRoot x ∈ square_roots S x)

include arbitraryRoot_root

end Construction

section ConcreteRefutations

lemma S.well_def (n : PNat) (hn : n.val ≠ 1) : 0 < n.val / (2 : Nat) := sorry

def S : PNat → PNat := fun n =>
  if h : n.val = 1 then 8 else ⟨n.val / (2 : Nat), S.well_def n h⟩

def arbitraryRoot : PNat → PNat := fun n =>
  n * 2

theorem arbitraryRoot_root : ∀ (x : PNat), arbitraryRoot x ∈ square_roots S x := sorry

end ConcreteRefutations

end Equation1447
