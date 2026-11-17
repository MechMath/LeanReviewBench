import Init.Core
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Order
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Rel
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Preorder.Chain
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith.Frontend
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

set_option backward.isDefEq.respectTransparency false

set_option backward.whnf.reducibleClassField false

noncomputable def Option.iget {α : Type*} [Nonempty α] (o : Option α) : α :=
  o.getD (Classical.choice inferInstance)

namespace Rel

variable {α β : Type*}

/-- Domain of a relation. -/
def dom (R : Rel α β) : Set α := {a | ∃ b, R a b}

/-- Codomain of a relation. -/
def codom (R : Rel α β) : Set β := {b | ∃ a, R a b}

end Rel

namespace Eq1516

open FreeGroup

open FreshGenerator

private abbrev A := FreeGroup Nat

private abbrev x : Nat → A := FreeGroup.of

private abbrev x₁ := x 1

private abbrev x₂ := x 2

private abbrev x₃ := x 3

private abbrev x₄ := x 4

private abbrev x₅ := x 5

private abbrev x₆ := x 6

private abbrev x₇ := x 7

/-- We will use `Finmap (fun _ : A => A)` to model the set E. There is no nondependent version of Finmap, so we have
to use a trivial Sigma type. -/
private abbrev TE := Finmap (fun _ : A => A)

notation:63 f:63 " ⬝ " a:64 => Finmap.lookup a f

instance inst_LE_TE: PartialOrder TE where
  le := fun E E' => ∀ {a a'}, a' ∈ E ⬝ a → a' ∈ E' ⬝ a
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

@[ext]
structure PartialSolution where
  E : TE
  --A partial solution is a function f : A → A satisfying certain invariants, with finite domain Dom.
  -- (1,1) ∈ E
  fId : 1 ∈ E ⬝ 1
  cond4 : ∀ a ∈ E, ∀ b ∈ E ⬝ a, ∀ c ∈ E ⬝ b,  a⁻¹ ∈ E ⬝ (c * a⁻¹)
  cond5 : ∀ a ∈ E, ∀ a' ∈ E, ∀ d ∈ E ⬝ (a⁻¹), ∀ d' ∈ E ⬝ (a'⁻¹),
     E ⬝ a = E ⬝ a' → d * a = d' * a' → a = a'
  cond6 : ∀ a ∈ E, a⁻¹ ∈ E ⬝ a → a = 1
  cond7 : ∀ a ∈ E, ∀ a' ∈ E, ∀ d ∈ E ⬝ a⁻¹, E ⬝ a = E ⬝ a' → a ≠ a' → d * a ≠ a'
  cond8 : ∀ a ∈ E, 1 ∈ E ⬝ a → a = 1

instance inst_LE_PartialSolution: PartialOrder PartialSolution where
  le x y := x.E ≤ y.E
  le_refl x := sorry
  le_trans a b c := sorry
  le_antisymm a b := sorry

def PartialSolution.Im (ps : PartialSolution) : Finset A :=
  (ps.E.entries.map Sigma.snd).toFinset

def helper {α β γ} (g : α → β) (f : ∀ b : α, γ (g b)) (h_g : Function.Injective g) (s : Finset α)
: Finmap γ where
  entries := Multiset.map (fun a => ⟨g a, f a⟩) s.1
  nodupKeys := by
    rw [← Multiset.nodup_keys]
    unfold Multiset.keys
    simp only [Multiset.map_map, Function.comp_apply]
    rw [Multiset.nodup_map_iff_of_injective]
    exact s.2
    exact h_g

def helper' {α β γ} (g : α → β) (f : ∀ b : α, γ (g b)) (s : Finset α) (d : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y)
: Finmap γ where
  entries := Multiset.map (fun a => ⟨g a, f a⟩) s.1
  nodupKeys := by
    rw [← Multiset.nodup_keys]
    unfold Multiset.keys
    simp only [Multiset.map_map, Function.comp_apply]
    rw [Multiset.nodup_map_iff_of_inj_on]
    exact s.2
    exact d

section extension

structure ExtensionTask where
  ps : PartialSolution
  b : A

namespace ExtensionTask

variable (t : ExtensionTask)

def preimages_of_b := t.ps.E.keys.filter (fun a' => t.b ∈ t.ps.E ⬝ a')

def s := t.preimages_of_b.filter (fun a' => a'⁻¹ ∈ t.ps.E)

def old := (t.ps.E.keys ∪ t.ps.Im) ∪ {t.b}

theorem dom_old'_subgroup {t : ExtensionTask} {x y : A} (h : y ∈ t.ps.E ⬝ x) : x ∈ Subgroup.closure t.old := sorry

theorem im_old_subgroup {t : ExtensionTask} {x y : A} (h : y ∈ t.ps.E ⬝ x) : y ∈ Subgroup.closure t.old := sorry

theorem b_old_subgroup : t.b ∈ Subgroup.closure t.old := sorry

macro "triv_subgroup" : tactic => `(tactic|
  first |
    (apply Subgroup.one_mem  ) |
    (apply im_old_subgroup ; tauto ) |
    (apply dom_old'_subgroup ; tauto) |
    (rw [← Subgroup.inv_mem_iff]; apply dom_old'_subgroup ; tauto) |
    (apply b_old_subgroup) |
    (rw [Subgroup.inv_mem_iff] ; apply b_old_subgroup)
    )

noncomputable def c := freshGenerator t.old

noncomputable def e0 : TE := Finmap.singleton t.b t.c

noncomputable def e1 : TE := helper (fun a' => t.c * a'⁻¹) (fun a' => a'⁻¹) (sorry) t.preimages_of_b

noncomputable def e2 : TE := helper' (fun a' => (t.ps.E ⬝ (a'⁻¹)).iget * a' * t.c⁻¹) (fun a' => a' *  t.c⁻¹) t.s (sorry
  )

noncomputable def newE : TE := t.ps.E ∪ t.e0 ∪ t.e1 ∪ t.e2

variable [b_not_in_dom : Fact (t.b ∉ t.ps.E)]

theorem newE_spec  : ∀ x y,  y ∈ t.newE ⬝ x ↔ ((((y ∈ t.ps.E ⬝ x) ∨ (x = t.b ∧ y = t.c)) ∨ (∃ a', t.b ∈ t.ps.E ⬝ a' ∧ t.c * a'⁻¹ = x ∧ a'⁻¹ = y))
∨ ∃ a' d', t.b ∈ t.ps.E ⬝ a' ∧ d' ∈ t.ps.E ⬝ (a'⁻¹) ∧  d' * a' * t.c⁻¹ = x ∧ a' * t.c⁻¹ = y) := sorry

include t in
theorem extension_cond4 : ∀ a ∈ t.newE, ∀ b ∈ t.newE ⬝ a, ∀ c ∈ t.newE ⬝ b, a⁻¹ ∈ t.newE ⬝ c * a⁻¹ := sorry

include t in
theorem extension_cond5 : ∀ a ∈ t.newE, ∀ a' ∈ t.newE, ∀ d ∈ t.newE ⬝ a⁻¹, ∀ d' ∈ t.newE ⬝ a'⁻¹, t.newE ⬝ a = t.newE ⬝ a' → d * a = d' * a' → a = a' := sorry

theorem extension_cond6 (a : A) : a ∈ t.newE → a⁻¹ ∈ t.newE ⬝ a → a = 1 := sorry

include t in
theorem extension_cond7  (a : A) :
  a ∈ t.newE → ∀ a' ∈ t.newE, ∀ d ∈ t.newE ⬝ a⁻¹, t.newE ⬝ a = t.newE ⬝ a' → a ≠ a' → d * a ≠ a' := sorry

theorem extension_cond8  (a : A) : a ∈ t.newE → 1 ∈ t.newE ⬝ a → a = 1 := sorry

noncomputable def extension : PartialSolution := by
  use t.newE
  case fId =>
    rw [newE_spec]
    simp [t.ps.fId]
  case cond4 => apply extension_cond4
  case cond5 => apply extension_cond5
  case cond6 => apply extension_cond6
  case cond7 => apply extension_cond7
  case cond8 => apply extension_cond8

end ExtensionTask

section extension2

namespace ExtensionTask

variable (t : ExtensionTask)

end ExtensionTask

end extension2

theorem extension2 (ps : PartialSolution) (b : A) (h : b ≠ 1) (n : Nat) :
∃ ps', ps ≤ ps' ∧ Finset.card {c ∈ ps'.E.keys | (b*c) ∈ ps'.E ⬝ c } ≥ n := sorry

def translation_invariant_1516 (f : A → A) : Prop := ∀ (x : A), (f ( f ( f x )* x⁻¹ * (f 1)⁻¹)) = x⁻¹ * (f 1)⁻¹

theorem completion (ps : PartialSolution) :
    ∃ (f : A → A), translation_invariant_1516 f ∧ (∀ x y, y ∈ ps.E ⬝ x → f x = y) ∧
      ∀ b, (b ≠ 1) → Set.encard {c | b * c = f c } ≥ 4 := sorry

def E0 : List (A × A) := [(1, 1), (x₁, x₂), (x₁⁻¹,x₃), (x₃ * x₁, x₄), (x₄ * x₂⁻¹, x₅),
  (x₆⁻¹, x₆^2), (x₆^3, x₆), (x₇⁻¹, x₇^2), (x₇^3, x₇)]

def initial : PartialSolution := by use List.toFinmap (E0.map Prod.toSigma) <;> decide

noncomputable def f := (completion initial).choose

end extension

noncomputable scoped instance magA : Magma A := { op := fun x y => f (y*x⁻¹) * x  }

section Refutation255

def G' := {(a, b, _) : A × A × ℕ | a ≠ b}

def G := A ⊕ G'

instance : Countable G' := sorry

instance : Countable G := sorry

instance : Infinite G := sorry

instance : Coe A G := ⟨.inl⟩

instance : Coe G' G := ⟨.inr⟩

/-- Square function: `S a = a ◇ a`.
On `A` it is the identity, on `G'` it corresponds to the function `(a, b, n) ↦ a`. -/
def S : G → A
  | .inl a => a
  | .inr g => g.1.1

def x₀ : G := .inr ⟨⟨1, x 0, 0⟩, fun h ↦ one_ne_of 0 h⟩

namespace GreedyB

lemma exists_useful_c (y : G') : ∃ c : A → A, c.Injective ∧
    ∀ b, y.1.1 ◇ ((c b) ◇ b) = c b ∧ c b ≠ b ∧ c b ≠ y.1.1 ∧ c b ≠ y.1.2.1 := sorry

noncomputable abbrev useful_c (y : G') : A → A := (exists_useful_c y).choose

structure OK (E : A → G → G → Prop) : Prop where
  func {a x y y'} : E a x y → E a x y' → y = y'
  extend (a b : A) : E a b (.inl (a ◇ b)) -- (a)
  h_b {a : A} {y : G'} : S y = a → y.1.2.2 = 0 → E a y a -- (b)
  h_c {a : A} {y : G'} : S y = a → y.1.2.2 ≠ 0 → E a y (.inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩) -- (c)
  h_d {b : A} {y : G'} : E (useful_c y b) y b -- (d)
  finite {a c : A} (hac : a ≠ c) : {n | ∃ x, E c (.inr ⟨⟨a, c, n⟩, hac⟩) x}.Finite -- (e)
  h_1516 {c' : A} {y : G'} {x : G} : E c' y x → ∃ w, E c' x w ∧ E (S y) w c' -- (f)
  h_g {c' : A} {y : G'} {x : G} : S y ≠ c' → E c' y x → x ≠ .inl c'

abbrev PartialSolution := {E : A → G → G → Prop // OK E}

/-- A partial soution, along with a pair `(d, g)` such that `L d g` is not yet defined. -/
class Extension1 where
  E : A → G → G → Prop
  ok : OK E
  d : A
  y : G'
  not_def {z} : ¬E d y z

/-- A partial solution, along with a pair `(a, y)` such that `L a y` is already defined and
`n ∈ ℕ`, a lower bound for the cardinality of `{z | E a z y}` after the extension step. -/
class Extension2 where
  E : A → G → G → Prop
  ok : OK E
  d : A
  y : G'
  g : G
  h_def : E d y g
  n : ℕ

namespace Extension1

variable [Extension1]

end Extension1

namespace Extension2

variable [Extension2]

end Extension2

theorem exists_extension (seed : PartialSolution) : ∃ L : A → G → G,
      (∀ a b : A, L a b = a ◇ b) ∧ -- Lb extends a : A ↦ b ◇ a
      (∀ b : A, ∀ x : G', (L (S x) <| L b <| L b x) = b) ∧ -- Axiom B
      (L 1 x₀ = .inl 1) ∧
      (∀ b : A, ∀ y : G', {z : G' | L b z = y}.Infinite) -- infinite surjectivity
    := sorry

@[mk_iff]
inductive seed : A → G → G → Prop
  | case0 (a b : A) : seed a b (.inl (a ◇ b))
  | case1 {c'} {y : G'} : S y = c' → y.1.2.2 = 0 → seed c' y c'
  | case2 {c'} {y : G'} : S y = c' → y.1.2.2 ≠ 0 → seed c' y (.inr ⟨⟨y.1.1, y.1.2.1, 0⟩, y.2⟩)
  | case3 (y : G') (b) : seed (useful_c y b) y b

lemma seed_ok : OK seed := sorry

noncomputable def L : A → G → G := (exists_extension ⟨seed, seed_ok⟩).choose

end GreedyB

namespace GreedyAC

open GreedyB

variable (x : G')

structure OK (E : Rel G G) : Prop where
  finite : Set.Finite {(x, y) : G × G | E x y}
  func {x y y'} : E x y → E x y' → y = y'
  inj {x x' y} : E x y → E x' y → x = x'
  aux1 : E x (S x) --Eq4 in the dim
  aux2 {y z w} : E y z → E z w → L (S y) w = x

abbrev PartialSolution := {E : Rel G G // OK x E}

class Extension where
  E : Rel G G
  ok : OK x E
  d : G
  not_def {y} : ¬E d y

namespace Extension

variable [Extension x]

/-- {y : G | ∃ z, E x y z} -/
def partial_domain' : Set G := (E x).dom

noncomputable instance : Fintype (partial_domain' x) := by
  suffices h : Set.Finite {z : G | ∃ y, E x z y} by exact h.fintype
  let f : G × G → G := fun x ↦ x.1
  have h1 : f '' {(z, y) : G × G | E x z y} ⊆ {z : G | ∃ (y : G) , E x z y} := by
    intro a ha
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists] at ha
    rcases ha with ⟨a1, a2, ha1, ha2⟩
    rw [← ha2]
    tauto
  have h2 : {z : G | ∃ y, E x z y} ⊆ f '' {(z, y) : G × G | E x z y} := by
    intro y hy
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists]
    rcases hy with ⟨y2, hy2⟩
    use y, y2
  exact h1.antisymm h2 ▸ Set.Finite.image f ok.finite

/-- {y : G | ∃ z, E x y z} as a Finset. -/
noncomputable def partial_domain : Finset G := (partial_domain' x).toFinset

/-- {z : G | ∃ y, E x y z} -/
def partial_range' : Set G := (E x).codom

noncomputable instance : Fintype (partial_range' x) := by
  suffices h : Set.Finite {y : G | ∃ z, E x z y} by exact h.fintype
  let f : G × G → G := fun x ↦ x.2
  have h1 : f '' {(z, y) : G × G | E x z y} ⊆ {y : G | ∃ z, E x z y} := by
    intro a ha
    simp only [Set.mem_image, Prod.exists, exists_eq_right] at ha
    simp_all [f]
  have h2 : {y : G | ∃ z, E x z y} ⊆ f '' {(z, y) : G × G | E x z y} := by
    intro y hy
    simp only [Set.mem_image, Prod.exists, exists_eq_right]
    simp_all [f]
  exact h1.antisymm h2 ▸ Set.Finite.image f ok.finite

/-- {z : G | ∃ y, E x y z} as a Finset. -/
noncomputable def partial_range : Finset G := (partial_range' x).toFinset

lemma exists_not_in_domain_range : ∃ w, w ∉ partial_domain x ∧ w ∉ partial_range x ∧ w ≠ d x := sorry

lemma exists_not_in_domain_range' (z : G) : ∃ w, L (S z) w = x ∧
    w ∉ partial_domain x ∧ w ∉ partial_range x ∧ w ≠ d x := sorry

/-- Given an extension, which is a partial solution with an undefined element of the domain
called `d`, we define a new element `w` that represents the image of `d` under `Lₓ`. -/
noncomputable def w : G := by
  classical
  exact if h : ∃ z, E x z (d x) then (exists_not_in_domain_range' x h.choose).choose
    else (exists_not_in_domain_range x).choose

@[mk_iff]
inductive Next : G → G → Prop
  | base {a b} : E x a b → Next a b
  | new : Next (d x) (w x)

theorem prev_w_is_d {y} : Next x y (w x) → y = d x
  := sorry

def next_finite : Set.Finite {(z, y) : G × G | Next x z y} := sorry

def next_func {z y y'} : Next x z y → Next x z y' → y = y'
  | .base hb, .base hb' => ok.func hb hb'
  | .new , .new  => rfl
  | .base hb, .new | .new, .base hb => (not_def hb).elim

def next_inj {z z' y} : Next x z y → Next x z' y → z = z'
  | .base hb, .base hb' => ok.inj hb hb'
  | .new, .new => rfl
  | .base hz, .new => prev_w_is_d _ (.base hz)
  | .new, .base hz' => (prev_w_is_d _ (.base hz')).symm

def next_aux1 : Next x x (S x) := Next.base ok.aux1

def next_aux2 {y z t} : Next x y z → Next x z t → L (S y) t = x := sorry

def next : PartialSolution x :=
  ⟨Next x, next_finite x, next_func x, next_inj x, next_aux1 x, next_aux2 x⟩

end Extension

theorem exists_extension (x : G') (seed : PartialSolution x) : ∃ Lₓ : G → G,
    Lₓ x = S x ∧ ∀ y, (L (S y) <| Lₓ <| Lₓ y) = x := sorry

end GreedyAC

open GreedyAC GreedyB

def seed (x : G') : Rel G G := fun a b ↦ a = x ∧ b = S x

theorem seed_ok (x : G') : OK x (seed x) := sorry

noncomputable def L' (x : G') : G → G := (exists_extension x ⟨seed x, seed_ok x⟩).choose

noncomputable scoped instance magG : Magma G := {
    op := fun x y =>
      match x with
      | .inl a => L a y
      | .inr g => L' g y
    }

end Refutation255

end Eq1516
