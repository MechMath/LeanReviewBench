import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Star
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.SimpleModule.Basic
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

set_option backward.isDefEq.respectTransparency false

abbrev G := (ℕ →₀ ℚ)

noncomputable abbrev n_q_basis := Finsupp.basisSingleOne (R := ℚ) (ι := ℕ)

noncomputable abbrev basis_n := DFunLike.coe n_q_basis

structure TreeData where
  a: G
  b: G

structure XVals where
  -- Represents the 'i' in the set 'S_i' from the paper. We use this to take elements from
  -- our basis that do not occur in any other `XVals`
  i: ℕ
  -- Our root element, determined when we recursively build up the partial function
  root_elem: G
  -- The paper requires that all of the 'x_i' elements (as well as the root 'a') are linearly independent.
  -- For convenience, we use a stronger condition: there is no overlap between root element coordinates
  -- (in the single element basis) and the coordinates of any of the 'x_i' elements.
  supp_gt: ∀ n, root_elem.support.max < (basis_n (2^(i) + n*2^(i+1))).support.min
  root_nonzero: i ≠ 0 → root_elem ≠ 0

noncomputable def XVals.x_vals (vals: XVals) (n: ℕ): G := if n = 0 then vals.root_elem else basis_n (2^(vals.i) + (n-1)*2^(vals.i+1))

noncomputable def XVals.x_to_index (vals: XVals) (n: ℕ): ℕ := (2^(vals.i) + n*2^(vals.i+1))

inductive TreeNode {vals: XVals} where
| root: TreeNode
| left: TreeNode → TreeNode
| right: TreeNode → TreeNode

def treeNum {vals: XVals}: @TreeNode vals → ℕ
  | TreeNode.root => 2
  | TreeNode.left prev => 2 * (treeNum prev) - 1
  | TreeNode.right prev => 2 * (treeNum prev)

noncomputable def TreeNode.getData {vals: XVals}: @TreeNode vals → TreeData
| TreeNode.root => {a := vals.root_elem, b := vals.x_vals 1}
| TreeNode.left base => {a := -base.getData.b, b := vals.x_vals (treeNum base)}
| TreeNode.right base => {a := vals.x_vals (treeNum base), b := base.getData.a - base.getData.b}

lemma tree_b_supp_nonempty {vals: XVals} (t: @TreeNode vals) : t.getData.b.support.Nonempty := sorry

def g_exclude := {g: G // g ≠ 0 }

noncomputable def biject_with_zero: Equiv G ℕ := by
  haveI g_exclude_countable: Countable g_exclude := Subtype.countable
  haveI g_exclude_infinite: Infinite g_exclude := sorry
  let default_equiv := Classical.choice (nonempty_equiv_of_countable (α := g_exclude) (β := ℕ))
  exact {
    toFun := fun g ↦ by
      by_cases g_eq_zero: g = 0
      · exact 0
      · exact 1 + default_equiv.toFun ⟨g, g_eq_zero⟩
    invFun := fun n => by
      by_cases n = 0
      · exact 0
      · exact (default_equiv.invFun (n - 1)).val
    left_inv := sorry
    right_inv := sorry
  }

@[irreducible] noncomputable def g_enumerate: ℕ → G := biject_with_zero.symm

@[irreducible] noncomputable def g_to_num (g: G): ℕ := biject_with_zero g

attribute [local instance] Classical.propDecidable

def finsuppHasNeg (g: G) := ∃ x ∈ (Set.range g), x < 0

def x_vals_zero: XVals := {
  i := 0
  root_elem := 0
  supp_gt := sorry
  root_nonzero := sorry
}

structure FData (g: G) where
  -- The previous `XVals` from the recursive construction of the function `f`.
  -- This includes whichever `XVals` contains a tree with an `a` value equal to `g`
  vals: Finset XVals
  -- Our chosen `XVals` and `TreeNode`, along with proofs about how they relate to the function argument `g`
  cur: XVals
  cur_in_vals: cur ∈ vals
  tree: @TreeNode cur
  a_val: tree.getData.a = g
  distinct_i: ∀ a ∈ vals, ∀ b ∈ vals, a.i = b.i → a = b
  distinct_trees: ∀ a ∈ vals, ∀ b ∈ vals, (∃ ta: @TreeNode a, ∃ tb: @TreeNode b, ta.getData.a = tb.getData.a) → a = b
  vals_has_zero : x_vals_zero ∈ vals
  -- Helper lemmas used for proving some non-implications - when we evaluate at concrete elements (e.g. `x_1 - x_3`),
  -- we can use this to bound the support of the resulting value, which will help us prove that the overall
  -- expression is not zero.
  supp_increasing: finsuppHasNeg tree.getData.a → tree.getData.a.support.max < tree.getData.b.support.max' (tree_b_supp_nonempty tree)
  supp_max_pos: finsuppHasNeg tree.getData.a → tree.getData.b (tree.getData.b.support.max' (tree_b_supp_nonempty tree)) > 0

noncomputable def f_data (n: ℕ): FData (g_enumerate n) := by
  match hn: n with
  | 0 =>
    exact {
      vals := {x_vals_zero},
      cur := x_vals_zero,
      cur_in_vals := sorry,
      tree := TreeNode.root,
      a_val := sorry
      distinct_i := sorry
      distinct_trees := sorry
      vals_has_zero := sorry
      supp_increasing := sorry
      supp_max_pos := sorry
  }
  | a + 1 =>
    -- Note - this would normally be a 'let', but this causes ea weird interaction with
    -- later 'omega' uses in this function:
    -- https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/'unexpected.20occurrence.20of.20recursive.20application'.20with.20omega
    have prev_x_vals := f_data a
    by_cases has_tree: ∃ x_vals: XVals, ∃ t: @TreeNode x_vals, x_vals ∈ prev_x_vals.vals ∧ t.getData.a = g_enumerate n
    · exact {
      vals := prev_x_vals.vals,
      cur := Classical.choose has_tree,
      vals_has_zero := prev_x_vals.vals_has_zero
      cur_in_vals := (Classical.choose_spec (Classical.choose_spec has_tree)).1,
      tree := Classical.choose (Classical.choose_spec has_tree)
      a_val := sorry
      distinct_i := prev_x_vals.distinct_i
      distinct_trees := prev_x_vals.distinct_trees
      supp_max_pos := sorry
      supp_increasing := sorry
    }
    · have img_nonempty : (prev_x_vals.vals.image XVals.i).Nonempty :=
        ⟨prev_x_vals.cur.i, Finset.mem_image.mpr ⟨prev_x_vals.cur, prev_x_vals.cur_in_vals, rfl⟩⟩
      let max_i := (prev_x_vals.vals.image XVals.i).max' img_nonempty
      let max_root_supp := ({(g_enumerate n).support.max.getD 0} ∪ (prev_x_vals.vals.image fun v => v.root_elem.support.max.getD 0)).max' (
        sorry
      )
      have g_supp_le: (g_enumerate n).support.max.getD 0 ≤ max max_i max_root_supp := by
        simp
        right
        simp [max_root_supp]
        apply Finset.le_max'
        simp
      have g_supp_lt: (g_enumerate n).support.max.getD 0 < max max_i max_root_supp + 1 := by omega
      have new_vals_not_supp: ∀ i, (2^(((max max_i max_root_supp) + 1)) + i*2^(((max max_i max_root_supp) + 1))) ∉ (g_enumerate n).support := by
        intro i
        have supp_max_lt: (g_enumerate n).support.max.getD 0 < (2 ^ (max max_i max_root_supp + 1)) := by
          have lt_self_pow := Nat.lt_pow_self Nat.one_lt_two (n := (max max_i max_root_supp + 1))
          omega
        apply Finset.notMem_of_max_lt_coe
        match h_supp_max: (g_enumerate n).support.max with
        | WithBot.some max_val =>
          norm_cast
          simp [h_supp_max] at supp_max_lt
          omega
        | ⊥ => exact WithBot.bot_lt_coe ..
      have new_vals_not_supp_double_plus: ∀ i, (2^(((max max_i max_root_supp) + 1)) + i*2^(((max max_i max_root_supp) + 1 + 1))) ∉ (g_enumerate n).support := by
        intro i
        have supp_max_lt: (g_enumerate n).support.max.getD 0 < (2 ^ (max max_i max_root_supp + 1)) := by
          have lt_self_pow := Nat.lt_pow_self Nat.one_lt_two (n := (max max_i max_root_supp + 1))
          omega
        apply Finset.notMem_of_max_lt_coe
        match h_supp_max: (g_enumerate n).support.max with
        | WithBot.some max_val =>
          norm_cast
          simp [h_supp_max] at supp_max_lt
          omega
        | ⊥ => exact WithBot.bot_lt_coe ..
      have lt_self_pow := Nat.lt_pow_self Nat.one_lt_two (n := (max max_i max_root_supp + 1))
      let new_x_vals: XVals := {
        i := ((max max_i max_root_supp) + 1)
        root_elem := g_enumerate n
        supp_gt := sorry
        root_nonzero := sorry
      }
      have prev_vals_root_not_supp: ∀ vals ∈ prev_x_vals.vals, ∀ i, (new_x_vals.x_to_index i) ∉ vals.root_elem.support := by
        intro vals h_vals i
        simp only [XVals.x_to_index, new_x_vals]
        have supp_max_lt: vals.root_elem.support.max.getD 0 < (2 ^ (max max_i max_root_supp + 1)) := by
          have le_max_plus: vals.root_elem.support.max.getD 0 ≤ max max_i max_root_supp := by
            simp
            right
            apply Finset.le_max'
            simp
            right
            use vals
          omega
        apply Finset.notMem_of_max_lt_coe
        match h_supp_max: vals.root_elem.support.max with
        | WithBot.some max_val =>
          simp [h_supp_max] at supp_max_lt
          rw [WithBot.coe_lt_coe]
          omega
        | ⊥ => apply WithBot.bot_lt_coe
      exact {
        vals := prev_x_vals.vals ∪ {new_x_vals},
        cur := new_x_vals,
        cur_in_vals := sorry,
        tree := TreeNode.root,
        supp_max_pos := sorry
        supp_increasing := sorry
        a_val := sorry
        vals_has_zero := Finset.mem_union_left {new_x_vals} prev_x_vals.vals_has_zero
        distinct_trees := sorry
        distinct_i := sorry
      }

noncomputable def f (g: G): G := (f_data (g_to_num g)).tree.getData.b
