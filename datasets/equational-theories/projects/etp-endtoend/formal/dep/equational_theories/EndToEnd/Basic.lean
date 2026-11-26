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

namespace Law

variable {G : Type} [Magma G]

/-- `G` satisfies every law in `ls`. -/
def SatisfiesAll (G : Type) [Magma G] : List (MagmaLaw ℕ) → Prop
  | [] => True
  | l :: ls => G ⊧ l ∧ SatisfiesAll G ls

/-- `G` refutes every law in `ls`. -/
def RefutesAll (G : Type) [Magma G] : List (MagmaLaw ℕ) → Prop
  | [] => True
  | l :: ls => ¬ (G ⊧ l) ∧ RefutesAll G ls

theorem SatisfiesAll.mem {ls : List (MagmaLaw ℕ)} (h : SatisfiesAll G ls) {l} (hl : l ∈ ls) :
    G ⊧ l := sorry

theorem RefutesAll.mem {ls : List (MagmaLaw ℕ)} (h : RefutesAll G ls) {l} (hl : l ∈ ls) :
    ¬ (G ⊧ l) := sorry

end Law

namespace EndToEnd

open Law

/-- The law at (0-based) index `i`, i.e. `Law{i+1}`. -/
abbrev lawOf (i : Nat) : Law.NatMagmaLaw := laws.get i

/-- A proven implication between two laws, carrying its proof. -/
structure PosFact where
  /-- the law assumed -/
  hyp : Nat
  /-- the law concluded -/
  conc : Nat
  proof : (lawOf hyp).implies (lawOf conc)

/-- A magma satisfying every law in `satisfies` and refuting every law in `refutes`, carrying its proof.
This is the deep-embedded form of a `Facts` theorem. -/
structure NegFact where
  /-- laws the magma satisfies -/
  satisfies : List Nat
  /-- laws the magma refutes -/
  refutes : List Nat
  h : ∃ (G : Type) (_ : Magma G),
        Law.SatisfiesAll G (satisfies.map lawOf) ∧ Law.RefutesAll G (refutes.map lawOf)

/-- A derivation of `lawOf n ⟹ lawOf m`: a list of indices into `pos`, composed left to right. -/
abbrev Implication := List Nat

/-- A refutation of `lawOf n ⟹ lawOf m`: the model witness `fact`, one law `a` it satisfies with
`a ⟹ n`, and one law `b` it refutes with `m ⟹ b`, each justified by an implication. -/
structure Refutation where
  fact : Nat
  a : Nat
  b : Nat
  up : Implication
  down : Implication
deriving Repr

variable (pos : RArray PosFact) (neg : RArray NegFact)

/-- Check that `c` derives `lawOf n ⟹ lawOf m` from `pos`. -/
def checkImplication (pos : RArray PosFact) : Nat → Nat → Implication → Bool
  | n, m, [] => n == m
  | n, m, k :: ks =>
      let f := pos.get k
      (f.hyp == n) && checkImplication pos f.conc m ks

/-- Check that `r` refutes `lawOf n ⟹ lawOf m` using `neg`. -/
def checkRefutation (n m : Nat) (r : Refutation) : Bool :=
  let f := neg.get r.fact
  f.satisfies.contains r.a && f.refutes.contains r.b
    && checkImplication pos r.a n r.up && checkImplication pos m r.b r.down

end EndToEnd
