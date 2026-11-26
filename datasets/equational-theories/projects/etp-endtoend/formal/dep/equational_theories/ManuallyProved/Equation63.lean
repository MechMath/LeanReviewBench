import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Order
import Mathlib.Data.Finset.Union
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Rel
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Preorder.Chain
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
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
import dep.equational_theories.FreshGenerator
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

namespace Eq63

private abbrev G := FreeGroup Nat

namespace Greedy

noncomputable section

open FreshGenerator

def thomson (f : G → G) := ∀ x, f (x⁻¹ * f (f x)) = x⁻¹

private abbrev g₁ := FreeGroup.of 1

private abbrev g₂ := FreeGroup.of 2

private abbrev g₃ := FreeGroup.of 3

private abbrev g₄ := FreeGroup.of 4

structure OK (E : Rel G G) : Prop where
  finite : Set.Finite {(x, y) : G × G | E x y}
  func {x y y'} : E x y → E x y' → y = y'
  base : E 1 g₁ ∧ E g₁ g₂ ∧ E g₂⁻¹ (g₁ * g₂) ∧ E (g₁ * g₂) (g₂⁻¹ * g₁)
  eq63 {x y z} : E x y → E y z → E (x⁻¹ * z) x⁻¹
  aux1 {x} : E x 1 → x = g₂
  aux2 {x} : ¬E x x⁻¹
  aux3 {x x' y z} : E x y → E x' y → E x⁻¹ z → x' = x * z → x' = x
  aux4 {x x' y z z'} : E x y → E x' y → E x⁻¹ z → E x'⁻¹ z' → x' * z' = x * z → x = x'

abbrev PartialSolution := {E : Rel G G // OK E}

class Extension where
  E : Rel G G
  ok : OK E
  d : G
  not_def {y} : ¬E d y

namespace Extension

variable [Extension]

def old : Finset G :=
  insert d <| ok.finite.toFinset.biUnion fun (a, b) => {a, b}

def c := FreeGroup.of (freshGeneratorName old)

@[mk_iff]
inductive Next : G → G → Prop
  | base {a b} : E a b → Next a b
  | new {a b} : a = d → b = c → Next a b
  | fromH {h a b} : E h d → a = h⁻¹ * c → b = h⁻¹ → Next a b
  | fromH' {h f a b} : E h d → E h⁻¹ f → a = c⁻¹ * h * f → b = c⁻¹ * h → Next a b

def next_finite : Set.Finite {(x, y) : G × G | Next x y} := sorry

def next_func {x y y'} : Next x y → Next x y' → y = y'
  | .base hb, .base hb' => ok.func hb hb'
  | .new rfl rfl, .new rfl rfl => rfl
  | .fromH h1 h2 h3, .fromH h1' h2' h3' => sorry
  | .base hb, .new rfl rfl | .new rfl rfl, .base hb => (not_def hb).elim
  | .base .., .fromH _ he _ | .fromH _ he _, .base ..| .new .., .fromH _ he _ | .fromH _ he _, .new ..
  | .base .., .fromH' _ _ he _ | .new .., .fromH' _ _ he _ | .fromH .., .fromH' _ _ he _
  | .fromH' _ _ he _, .base .. | .fromH' _ _ he _, .new .. | .fromH' _ _ he _, .fromH .. => sorry
  | .fromH' h1 h2 h3 rfl, .fromH' h1' h2' rfl rfl => sorry

def next_base : Next 1 g₁ ∧ Next g₁ g₂ ∧ Next g₂⁻¹ (g₁ * g₂) ∧ Next (g₁ * g₂) (g₂⁻¹ * g₁) := sorry

def next_eq63 {x y z} : Next x y → Next y z → Next (x⁻¹ * z) x⁻¹
  | .base hb, .base hb' => .base $ ok.eq63 hb hb'
  | .base hb, .new rfl rfl => .fromH hb rfl rfl
  | .fromH h rfl h', .base hb => sorry
  | .fromH h rfl h', .new rfl rfl => False.elim $ ok.aux2 (h' ▸ h)
  | .new rfl rfl, .fromH h1 h2 rfl => sorry
  | .fromH' _ _ rfl rfl, .fromH' _ _ he rfl => sorry
  | .base .., .fromH .. | .base .., .fromH' .. | .new .., .base .. | .fromH' .., .base .. => sorry
  | .new .., .new he _ | .new .., .fromH' _ _ he _ | .fromH _ _ he, .fromH ..
  | .fromH _ _ he, .fromH' .. | .fromH' .., .new he _ | .fromH' .., .fromH _ he _ => sorry

def next_aux1 {x} : Next x 1 → x = g₂
  | .base hb => ok.aux1 hb
  | .new rfl h => sorry
  | .fromH h1 rfl h2 => sorry
  | .fromH' _ _ rfl he => sorry

def next_aux2 {x} : ¬Next x x⁻¹
  | .base hb => ok.aux2 hb
  | .new _ he | .fromH _ he _ | .fromH' _ _ _ he => sorry

def next_aux3 {x x' y z} : Next x y → Next x' y → Next x⁻¹ z → x' = x * z → x' = x := sorry

def next_aux4 {x x' y z z'} : Next x y → Next x' y → Next x⁻¹ z → Next x'⁻¹ z' → x' * z' = x * z → x = x' := sorry

def next : PartialSolution :=
  ⟨Next, next_finite, fun {_} => next_func, next_base, next_eq63, next_aux1, next_aux2, next_aux3, next_aux4⟩

end Extension

theorem exists_extension (seed : PartialSolution) :
    ∃ f : G → G,
    thomson f ∧
    (∀ {x y}, seed.1 x y → f x = y) := sorry

end

end Greedy

open Greedy

def seed' : List (G × G) := [
  (1, g₁), (g₁, g₂), (g₂, 1), (g₁⁻¹, g₁⁻¹), (g₂⁻¹ * g₁, g₂⁻¹), (g₂⁻¹, g₁ * g₂),
  (g₁⁻¹ * g₂ * g₁ * g₂, g₁⁻¹ * g₂), (g₁ * g₂, g₂⁻¹ * g₁), (g₂⁻¹ * g₁⁻¹ * g₂⁻¹, g₂⁻¹ * g₁⁻¹),
  (g₃, g₄⁻¹), (g₄, g₃), (g₄⁻¹^2, g₄⁻¹),
]

def seed : Rel G G := fun x y => (x, y) ∈ seed'

end Eq63
