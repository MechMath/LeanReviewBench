import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
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

namespace ThreeC2

/-- Free words over three generators -/
abbrev W := List (Fin 3)

/-- List reversal is going to be our inverse, so let's introduce convenient notation. -/
local notation x "⁻¹" => List.reverse x

/-- Reduced words do not have the same element adjacent to each other -/
def IsRed (w : W) : Prop := ∀ i, (h : i + 1 < w.length) → w[i] ≠ w[i+1]

@[simp]
theorem IsRed_singleton x : IsRed [x] := sorry

theorem IsRed_uncons {x} {ys} (h : IsRed (x :: ys)) : IsRed ys := sorry

theorem IsRed_cons {y} {x} {ys} (hne : y ≠ x) (h : IsRed (x :: ys)) : IsRed (y :: x :: ys) := sorry

def red (w : W) : W := go [] w
where
  -- A zipper processing helper function.
  go : (ys xs : W) → W
     | ys, []       => ys.reverse
     | [],    x::xs => go [x] xs
     | y::ys, x::xs =>
      if x = y then
        go ys xs
      else
        go (x::y::ys) xs

  -- Neat trick: We define a copy of that function that passes through the `IsRed` assumption.
  -- We do not use this function, but we can use its induction principle to do proofs about
  -- `red.go` without having to thread through this assumption manually, if we need that.
  go_aux : (ys xs : W) → (h : IsRed ys) → W
     | ys, [], _       => ys.reverse
     | [],    x::xs, _ => go_aux [x] xs (IsRed_singleton _)
     | y::ys, x::xs, h =>
      if heq : x = y then
        go_aux ys xs (IsRed_uncons h)
      else
        go_aux (x::y::ys) xs (IsRed_cons heq h)

@[simp]
theorem red_IsRed (w : W) : IsRed (red w) := sorry

attribute [simp] List.reverse_append

/-- The `f` function that we use to define the monoid of interest -/
def f : W → W
  | [] => []
  | [x] => [x+1]
  | x::_::_ => [x]

attribute [simp] f.eq_1 f.eq_2

/-- The carrier for our magma: reduced words -/
abbrev M := {x : W // IsRed x}

/-- The magma instance -/
instance inst : Magma M where
  op := fun ⟨x, _⟩ ⟨y, _⟩ =>
    ⟨red (x ++ f (red (x.reverse ++ y))), red_IsRed _⟩

theorem Fact : ∃ (G : Type) (_ : Magma G), Facts G [206] [1648] := sorry

/-- We use a variant of the above construction to show that 1841 does not imply 203. We use as the
underlying magma M × Bool -/

def g : W → W
  | [] => [1]
  | x::__ => [x]

abbrev M2 := {x : W × Bool // IsRed x.1 }

instance inst2 : Magma M2 where
  op x y := match x, y with
  | ⟨(x, true), hx⟩ , _ => ⟨(x, true), hx⟩
  | ⟨(x, false), _⟩, ⟨(y, true), _⟩ => ⟨(red (x ++ g (red (x.reverse ++ y))),  false), red_IsRed _⟩
  | ⟨(x, false), hx⟩, ⟨(y,false), _⟩ =>
    if x = y then ⟨(x, true), hx⟩ else ⟨(red (x ++ f (red (x.reverse ++ y))), false), red_IsRed _⟩

end ThreeC2
