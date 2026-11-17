import Init.Classical
import Init.Prelude
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.Countable.Defs
import Mathlib.Data.DFinsupp.Encodable
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.WithBot
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic
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
import dep.equational_theories.ManuallyProved.Equation1729.SmallMagma
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder

set_option backward.isDefEq.respectTransparency false

set_option backward.whnf.reducibleClassField false

set_option maxHeartbeats 2000000

namespace Eq1729

abbrev axiom_i'' (L₀' : N → N) (Predom : Finset N) := ∀ (x y : N) (_: x ∈ Predom) (_ : L₀' x = y) (n:ℤ), y ∈ fill Predom ∧ L₀' ((e 0)^n * x) = (e 0)^n * y ∧ L₀' ((e 0)^n * y) = (e 0)^(n-1) * x

class PartialSolution where
  L₀' : N → N
  op : N → N → M
  S' : N → SM
  I : Finset (N × N × N)
  Predom_L₀' : Finset N
  Dom_op : Finset (N × N)
  Dom_S' : Finset N
  axiom_i'' : axiom_i'' L₀' Predom_L₀'
  axiom_S (x y : N) (h : x ∈ Dom_S') (h' : y ≤ x) : y ∈ Dom_S'
  axiom_iii'' (x y : N) (a : SM) (hx: x ∈ Dom_S') (hy: y ∈ Dom_S') (h: R' a x = y) : R' (S (a - S' x)) y ∈ fill Predom_L₀' ∧ (R' (S (S' y)) <| (R' (a - S' x)).symm <| L₀' <| R' (S (a - S' x)) y ) ∈ fill Predom_L₀' ∧ ((R' (S' y)).symm <| L₀' <| R' (S (S' y)) <| (R' (a - S' x)).symm <| L₀' <| R' (S (a - S' x)) y ) = x
  axiom_iv'' (x : N) (h : x ∈ Dom_S') : R' (S (S' x)) x ∈ fill Predom_L₀' ∧ (R' (S (S' x)) <| (R' (S' x)).symm <| L₀' <| R' (S (S' x)) x) ∈ fill Predom_L₀' ∧ ((R' (S' x)).symm <| L₀' <| R' (S (S' x)) <| (R' (S' x)).symm <| L₀' <| R' (S (S' x)) x) = x
  axiom_v'' (x : N) (h : (x,x) ∈ Dom_op) : x ∈ Dom_S' ∧ op x x = Sum.inl (S' x)
  axiom_vi'' (y : N) (a : SM) (h: (R' a y, y) ∈ Dom_op) : y ∈ Dom_S' ∧ op (R' a y) y = Sum.inl ( a - S' y )
  axiom_vii'' (x y : N) (h : x ≠ y) (h' : ∀ a : SM, x ≠ R' a y) (hop: (x,y) ∈ Dom_op) : ∃ z : N, op x y = Sum.inr z ∧ ((x,y,z) ∈ I ∨ ((z,x) ∈ Dom_op ∧ x ∈ Dom_S' ∧ (R' 0 <| R' (S' x) <| y) ∈ fill Predom_L₀' ∧ op z x = Sum.inr ((R' (S (S' x))).symm <| L₀' <| R' 0 <| R' (S' x) <| y)))
  axiom_P (x y z : N) (h: (x,y,z) ∈ I) : x ∉ Dom_S' ∧ (z,x) ∉ Dom_op ∧ z ≠ x ∧ (∀ a : SM, z ≠ R' a x ∧ R' a z ≠ x) ∧ (y ≠ x) ∧ (y ≠ parent x)
  axiom_P' (x y y' z : N) (hy : (x,y,z) ∈ I) (hy' : (x,y',z) ∈ I) : y = y'
  axiom_P'' (x y z : N) (hy : (x,y,z) ∈ I) : (x,y) ∈ Dom_op ∧ Sum.inr z = op x y
  axiom_L (x y₀:N) (a : SM) (hpar: y₀ = parent x) (hS : y₀ ∈ Dom_S') (h: R' (S (a - S' y₀)) x ∈ fill Predom_L₀') (ha: x = R' a y₀): ((R' (a - S' y₀)).symm <| L₀' <| R' (S (a - S' y₀)) <| x) ≠ x

instance PartialSolution_LE : LE PartialSolution  := {
  le := by
    intro sol1 sol2
    exact sol1.Predom_L₀' ⊆ sol2.Predom_L₀' ∧ sol1.Dom_op ⊆ sol2.Dom_op ∧ sol1.Dom_S' ⊆ sol2.Dom_S' ∧ (∀ x, x ∈ fill sol1.Predom_L₀' → sol1.L₀' x = sol2.L₀' x) ∧ (∀ z ∈ sol1.Dom_op, sol1.op z.1 z.2 = sol2.op z.1 z.2) ∧ (∀ x ∈ sol1.Dom_S', sol1.S' x = sol2.S' x)
}

lemma PartialSolution.refl (sol : PartialSolution) : sol ≤ sol := sorry

/-- Impose a preorder on solutions using the notion of an extension· -/
instance PartialSolution_order : Preorder PartialSolution  := {
  le := PartialSolution_LE.le
  le_refl := PartialSolution.refl
  le_trans := sorry
}

noncomputable abbrev Set.choose {α: Type} {S: Set α} {P: α → Prop} (h: ∃ s ∈ S, P s) : S := ⟨_, (Classical.choose_spec h).1⟩

lemma Set.choose_spec {α: Type} {S: Set α} {P: α → Prop} (h: ∃ s ∈ S, P s) : P (Set.choose h) := sorry

/-- All the elements of `SM` that are involved in a partial solution, plus an additional set of extra elements of `N`-/
abbrev PartialSolution.involved_elements (sol: PartialSolution) (extras: Finset M) : Finset SM := Finset.biUnion sol.Predom_L₀' basis_elements ∪ Finset.biUnion sol.Dom_S' basis_elements ∪ Finset.image  sol.S' sol.Dom_S' ∪ Finset.biUnion sol.Dom_op (fun (x, _) ↦ basis_elements x) ∪ Finset.biUnion sol.Dom_op (fun (_, y) ↦ basis_elements y) ∪ Finset.biUnion sol.Dom_op (fun (x, y) ↦ basis_elements' (sol.op x y)) ∪ Finset.biUnion sol.I (fun (x, _, _) ↦ basis_elements x) ∪ Finset.biUnion sol.I (fun (_, y, _) ↦ basis_elements y) ∪ Finset.biUnion sol.I (fun (_, _, z) ↦ basis_elements z) ∪ Finset.biUnion extras basis_elements'

abbrev PartialSolution.reaches (sol: PartialSolution) (extras: Finset M) (a : SM) := in_generators (sol.involved_elements extras) a

abbrev PartialSolution.fresh_generator (sol : PartialSolution) (extras: Finset M) (n:ℕ) : ℕ := fresh (sol.involved_elements extras) n

open Classical in
/-- Extend a map L₀' to map (R' 0)^n x to (R' 0)^n y and (R' 0)^n y to (R' 0)^(n-1) x for all integers n·  One should also add x and y to the predomain when extending· -/
noncomputable abbrev PartialSolution.extend {sol:PartialSolution} (x y:N) (z : N): N :=
  if z ≈ x then z * x⁻¹ * y else (if z ≈ y then z * y⁻¹ * (e 0)⁻¹ * x else sol.L₀' z)

class PartialSolution_with_axioms extends PartialSolution where
  x : N
  hx : x ∉ Dom_S'
  hind : ∀ y:N, y < x → y ∈ Dom_S'
  hA : ∀ a, R' a x = parent x → R' (S' (parent x)) x ∈ fill Predom_L₀'
  hB : ∀ a, x = R' a (parent x) → R' (S a + S (S' (parent x))) x ∈ fill Predom_L₀'
  hC : ∀ y z, (x,y,z) ∈ I → z ∈ Dom_S' → R' 0 (R' (S' z) x) ∈ fill Predom_L₀'

abbrev PartialSolution_with_axioms.y₀ (sol : PartialSolution_with_axioms) : N := parent sol.x

open Classical

noncomputable abbrev PartialSolution_with_axioms.a_right (sol : PartialSolution_with_axioms) : SM := if h : ∃ a, sol.x = R' a sol.y₀ then h.choose else 0

noncomputable abbrev PartialSolution_with_axioms.a_left (sol : PartialSolution_with_axioms) : SM := if h : ∃ a, R' a sol.x = sol.y₀ then h.choose else 0

noncomputable abbrev PartialSolution_with_axioms.extras (sol : PartialSolution_with_axioms) : Finset M := {Sum.inr sol.x, Sum.inr sol.y₀, Sum.inl (sol.S' sol.y₀), Sum.inl sol.a_left, Sum.inl sol.a_right}

/-- Data type to store the various L₀' extensions needed to prove `enlarge_S'_induction_with_axioms` -/
inductive L₀'_data (sol : PartialSolution_with_axioms) where
  | iv₁ : L₀'_data sol
  | iv₂ : L₀'_data sol
  | iii₁ (a : SM) (ha: R' a sol.x = sol.y₀) : L₀'_data sol
  | iii₂ (a : SM) (ha: sol.x = R' a sol.y₀) : L₀'_data sol
  | P (y z:N) (hI: (sol.x,y,z) ∈ sol.I) : L₀'_data sol

noncomputable instance  (sol : PartialSolution_with_axioms) : Fintype (L₀'_data sol) := by
  set embed : L₀'_data sol → Fin 4 ⊕ sol.I := fun data ↦ match data with
  | L₀'_data.iv₁ => Sum.inl 0
  | L₀'_data.iv₂ => Sum.inl 1
  | L₀'_data.iii₁ a ha => Sum.inl 2
  | L₀'_data.iii₂ a ha => Sum.inl 3
  | L₀'_data.P y z hI => Sum.inr ⟨(sol.x,y,z), hI⟩
  refine Fintype.ofInjective embed fun data data' h ↦ ?_
  rcases data with ⟨⟩ | ⟨⟩ | ⟨a,ha⟩ | ⟨a,ha⟩ | ⟨y,z,hI⟩
  all_goals rcases data' with ⟨⟩ | ⟨⟩ | ⟨a',ha'⟩ | ⟨a',ha'⟩ | ⟨y',z',hI'⟩
  all_goals simp [embed] at h ⊢
  · exact R'_axiom_iia'.mp (ha' ▸ ha)
  · exact R'_axiom_iia'.mp (ha ▸ ha')
  · exact h

/-- Data type to store the various op extensions needed to prove `enlarge_S'_induction_with_axioms` -/
inductive op_data (sol: PartialSolution_with_axioms) where
  | old (y z:N) (hop: (y,z) ∈ sol.Dom_op) : op_data sol
  | v : op_data sol
  | P₁ (y z:N) (hI: (sol.x,y,z) ∈ sol.I)  : op_data sol
  | P₂ (y z:N) (hI: (sol.x,y,z) ∈ sol.I) (hz : z ∈ sol.Dom_S') : op_data sol

noncomputable instance  (sol : PartialSolution_with_axioms) : Fintype (op_data sol) := by
  set embed : op_data sol → sol.Dom_op ⊕ Fin 1 ⊕ sol.I ⊕ sol.I := fun data ↦ match data with
  | op_data.old y z hop => Sum.inl ⟨(y,z), hop⟩
  | op_data.v => Sum.inr <| Sum.inl 0
  | op_data.P₁ y z hI => Sum.inr <| Sum.inr <| Sum.inl ⟨(sol.x,y,z), hI⟩
  | op_data.P₂ y z hI hz => Sum.inr <| Sum.inr <| Sum.inr ⟨(sol.x,y,z), hI⟩
  refine Fintype.ofInjective embed fun data data' h ↦ ?_
  rcases data with ⟨y,z,hop⟩ | ⟨⟩ | ⟨y,z,hI⟩ | ⟨y,z,hI,hz⟩
  all_goals rcases data' with ⟨y',z',hop'⟩ | ⟨⟩ | ⟨y',z',hI'⟩ | ⟨y',z',hI',hz'⟩
  all_goals simp [embed] at h ⊢
  all_goals exact h

/-- Data type to store the various I extensions needed to prove `enlarge_S'_induction_with_axioms` -/
inductive I_data (sol: PartialSolution_with_axioms) where
  | old (x' y z:N) (hI: (x',y,z) ∈ sol.I) (hxx': sol.x ≠ x') : I_data sol
  | P₁ (y z:N) (hI: (sol.x,y,z) ∈ sol.I) (hz : z ∉ sol.Dom_S') : I_data sol
  | P₂ (y z:N) (hI: (sol.x,y,z) ∈ sol.I) (hz : z ∈ sol.Dom_S') : I_data sol

noncomputable instance  (sol : PartialSolution_with_axioms) : Fintype (I_data sol) := by
  set embed : I_data sol → sol.I ⊕ sol.I ⊕ sol.I := fun data ↦ match data with
  | I_data.old x' y z hI hxx' => Sum.inl ⟨(x',y,z), hI⟩
  | I_data.P₁ y z hI hz => Sum.inr <| Sum.inl ⟨(sol.x,y,z), hI⟩
  | I_data.P₂ y z hI hz => Sum.inr <| Sum.inr ⟨(sol.x,y,z), hI⟩
  refine Fintype.ofInjective embed fun data data' h ↦ ?_
  rcases data with ⟨x',y,z,hI,hxx'⟩ | ⟨y,z,hI,hz⟩ | ⟨y,z,hI,hz⟩
  all_goals rcases data' with ⟨x'',y',z',hI',hxx''⟩ | ⟨y',z',hI',hz'⟩ | ⟨y',z',hI',hz'⟩
  all_goals { simp [embed] at h ⊢ ; try exact h }

noncomputable def  enum : N × N → ℕ := fun  p ↦ Exists.choose (Countable.exists_injective_nat (N × N)) p + 2

noncomputable abbrev PartialSolution_with_axioms.m (sol: PartialSolution_with_axioms) (i:ℕ) := sol.fresh_generator sol.extras i

noncomputable abbrev PartialSolution_with_axioms.d (sol: PartialSolution_with_axioms) (y z: N) := E (sol.m (enum (y,z)))

open PartialSolution_with_axioms

end Eq1729
