import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Basic.Denumerable
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Recall
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.FactsSyntax
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

recall Equation65 (G : Type _) [Magma G] := ∀ x y : G, x = y ◇ (x ◇ (y ◇ x))

namespace Asterix

variable {G : Type*} [DecidableEq G]

variable (G) in
@[ext]
structure PartialSolution where
  E0 : Finset (G × G)
  E1 : Finset (G × G)
  f : G → G → G
  E0_subset_E1 : E0 ⊆ E1
  t_mem_of_mem_E0' : ∀ x ∈ E0, (x.2, f x.1 x.2) ∈ E1
  mem_2_of_mem_E0 : ∀ x ∈ E0, (x.1, f x.2 (f x.1 x.2)) ∈ E1
  eq_of_mem_E0 : ∀ x ∈ E0, f x.1 (f x.2 (f x.1 x.2)) = x.2
  undef_of_not_mem_E0' : ∀ x ∈ E1 \ E0, (x.2, f x.1 x.2) ∉ E1
  strange: ∀ x ∈ E1, f x.1 x.2 = x.1 → ((x.2, x.2) ∈ E1 ∧ f x.2 x.2 = x.1)

abbrev PartialSolution.g (f : PartialSolution G) : G × G → G × G :=
  fun (x, y) => (y, f.f x y)

instance : Preorder (PartialSolution G) where
  le a b := a.E0 ≤ b.E0 ∧ a.E1 ≤ b.E1 ∧ Set.EqOn a.f.uncurry b.f.uncurry a.E1
  le_refl := sorry
  le_trans a b c hab hbc := sorry

def PartialSolution.move_rev_good (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) : PartialSolution G :=
  let f' y' x' := if y' = y ∧ x' = x then z else if x' = z then y else f.f y' x'
  have f'_of_mem_E1 {a b : G} (ha : (a, b) ∈ f.E1) : f' a b = f.f a b := sorry
  have f'_of_mem_E0 {a b : G} (ha : (a, b) ∈ f.E0) : f' a b = f.f a b := f'_of_mem_E1 (f.E0_subset_E1 ha)
  have f'_y_x : f' y x = z := sorry
  have f'_z {a : G} : f' a z = y := sorry
  {
  E0 := f.E0 ∪ (f.E1.filter fun ⟨y', x'⟩ ↦ x' = y ∧ f.f y' x' = x)
  E1 := f.E1 ∪ {(y, x), (z, z)} ∪ (f.E1.filter fun ⟨y', x'⟩ ↦ x' = y ∧ f.f y' x' = x).image fun ⟨y', _⟩ ↦ (y', z)
  f := f'
  E0_subset_E1 := sorry
  t_mem_of_mem_E0' := sorry
  mem_2_of_mem_E0 := sorry
  eq_of_mem_E0 := sorry
  undef_of_not_mem_E0' := sorry
  strange := sorry
  }

def PartialSolution.move_rev_bad (f : PartialSolution G) (x y : G) (z : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) (hz1 : ∀ x ∈ f.E1, x.2 ≠ z)
    (hz2 : ∀ x ∈ f.E1, f.f x.1 x.2 ≠ z) (hz3 : ∀ x ∈ f.E1, x.1 ≠ z)
    (hzx : z ≠ x) (hzy : z ≠ y) : PartialSolution G :=
  let f' y' x' := if y' = y ∧ x' = x then z else if x' = z then y else f.f y' x'
  have f'_of_mem_E1 {a b : G} (ha : (a, b) ∈ f.E1) : f' a b = f.f a b := sorry
  have f'_of_mem_E0 {a b : G} (ha : (a, b) ∈ f.E0) : f' a b = f.f a b := f'_of_mem_E1 (f.E0_subset_E1 ha)
  have f'_y_x : f' y x = z := sorry
  have f'_z {a : G} : f' a z = y := sorry
  {
  E0 := f.E0 ∪ {(y, x)} ∪ (f.E1.filter fun ⟨y', x'⟩ ↦ x' = y ∧ f.f y' x' = x)
  E1 := f.E1 ∪ {(y, x), (z, z)} ∪ (f.E1.filter fun ⟨y', x'⟩ ↦ x' = y ∧ f.f y' x' = x).image fun ⟨y', _⟩ ↦ (y', z)
  f := f'
  E0_subset_E1 := sorry
  t_mem_of_mem_E0' := sorry
  mem_2_of_mem_E0 := sorry
  eq_of_mem_E0 := sorry
  undef_of_not_mem_E0' := sorry
  strange := sorry
  }

variable [Denumerable G]

def Denumerable.notMemFinset (s : Finset G) : G :=
  Denumerable.ofNat G (Nat.find (Infinite.exists_notMem_finset (s.image Encodable.encode)))

omit [DecidableEq G] in
theorem Denumerable.notMemFinset_prop (s : Finset G) : Denumerable.notMemFinset s ∉ s := sorry

def PartialSolution.move_rev_good' (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1 → f.f x y ≠ x) : PartialSolution G := by -- This intentionally used `by` for data.
  let z : G := Denumerable.notMemFinset (f.E1.image (·.1) ∪ f.E1.image (·.2) ∪ f.E1.image (fun ⟨a, b⟩ ↦ f.f a b) ∪ {x, y})
  have zp := Denumerable.notMemFinset_prop (f.E1.image (·.1) ∪ f.E1.image (·.2) ∪ f.E1.image (fun ⟨a, b⟩ ↦ f.f a b) ∪ {x, y})
  change z ∉ _ at zp
  simp only [Finset.union_assoc, Finset.union_insert, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, Finset.mem_singleton, not_or,
    not_exists, not_and] at zp
  exact f.move_rev_good x y z h1 h2 (fun x hx nh ↦ zp.2.2.1 x.1 (sorry))
    (fun x hx ↦ zp.2.2.2.1 x.1 x.2 hx) (fun x hx nh ↦ zp.2.1 x.2 (sorry)) zp.1 zp.2.2.2.2

def PartialSolution.move_rev_bad' (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1)
    (h2 : (x, y) ∈ f.E1) (h22 : f.f x y = x) : PartialSolution G := by
  let z : G := Denumerable.notMemFinset (f.E1.image (·.1) ∪ f.E1.image (·.2) ∪ f.E1.image (fun ⟨a, b⟩ ↦ f.f a b) ∪ {x, y})
  have zp := Denumerable.notMemFinset_prop (f.E1.image (·.1) ∪ f.E1.image (·.2) ∪ f.E1.image (fun ⟨a, b⟩ ↦ f.f a b) ∪ {x, y})
  change z ∉ _ at zp
  simp only [Finset.union_assoc, Finset.union_insert, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, Finset.mem_singleton, not_or,
    not_exists, not_and] at zp
  exact f.move_rev_bad x y z h1 h2 h22 (fun x hx nh ↦ zp.2.2.1 x.1 (sorry))
    (fun x hx ↦ zp.2.2.2.1 x.1 x.2 hx) (fun x hx nh ↦ zp.2.1 x.2 (sorry)) zp.1 zp.2.2.2.2

def PartialSolution.act (f : PartialSolution G) (x y : G) (h1 : (y, x) ∉ f.E1) : PartialSolution G :=
    if h2 : (x, y) ∈ f.E1 → f.f x y ≠ x then f.move_rev_good' x y h1 h2
      else f.move_rev_bad' x y h1 (sorry) (sorry)

def PartialSolution.add_e1 (f : PartialSolution G) (x y : G) : PartialSolution G :=
    if h1 : (y, x) ∈ f.E1 then f else f.act x y h1

def PartialSolution.add_e0 (f : PartialSolution G) (x y : G) : PartialSolution G :=
  let f' := f.add_e1 x y
  f'.add_e1 (f'.f y x) x

def closureSeq (f : PartialSolution G) : ℕ → PartialSolution G
| 0 => f
| n+1 => (closureSeq f n).add_e0 (Denumerable.ofNat (G × G) n).2 (Denumerable.ofNat (G × G) n).1

def closure (f : PartialSolution G) : G → G → G :=
  fun a b ↦ (closureSeq f (Encodable.encode (a, b) + 1)).f a b
