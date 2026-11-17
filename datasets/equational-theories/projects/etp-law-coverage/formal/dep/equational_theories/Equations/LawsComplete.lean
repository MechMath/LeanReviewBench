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
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.RArray

open Lean Elab in
/--
An elaborator to assemble all the separate `Law{n}` definitions into one data structure.
-/
elab "defineLaws%" : term => do
  let consts : _root_.RArray Expr := RArray.ofFn (h := by omega) fun (⟨i, _⟩ : Fin 4694) =>
    mkConst (.mkSimple s!"Law{i+1}")
  return consts.toExpr (mkConst ``Law.NatMagmaLaw) id

set_option maxRecDepth 15000 in
/--
All the separate `Law{n}` definitions in one data structure.

```
example : laws[1000] = Law1001 := rfl
```
-/
def laws : RArray Law.NatMagmaLaw := defineLaws%

def FreeMagma.cmpShape {α β} (l1 : FreeMagma α) (l2 : FreeMagma β) : Ordering :=
  (compare l1.forks l2.forks).then <|
    match l1, l2 with
    | .Leaf _,     .Leaf _     => .eq
    | .Leaf _,     .Fork _ _   => .lt
    | .Fork _ _,   .Leaf _     => .gt
    | .Fork l1 r1, .Fork l2 r2 => (l1.cmpShape l2).then (r1.cmpShape r2)

def List.cmp {α} [Ord α] : List α → List α → Ordering
  | [], [] => .eq
  | [], _::_ => .lt
  | _::_, [] => .gt
  | a::as, b::bs => (compare a b).then (List.cmp as bs)

instance {α} [Ord α] : Ord (List α) := ⟨List.cmp⟩

/-- An ordering on `FreeMagma` that coincides with the order we put the laws in.  -/
def FreeMagma.cmp {α} [LinearOrder α] (m1 m2 : FreeMagma α) : Ordering :=
  (m1.cmpShape m2).then (m1.toList.cmp m2.toList)

/-- The number of forks in a magma law. -/
def Law.MagmaLaw.forks {α} (l : Law.MagmaLaw α) : Nat :=
  l.lhs.forks + l.rhs.forks

def Law.MagmaLaw.cmpShape {α β} (l1 : Law.MagmaLaw α) (l2 : Law.MagmaLaw β) : Ordering :=
 (FreeMagma.cmpShape l1.lhs l2.lhs).then (FreeMagma.cmpShape l1.rhs l2.rhs)

/-- An ordering on `NatMagmaLaw` that coincides with the order we put the laws in.  -/
def Law.MagmaLaw.cmp {α} [LinearOrder α] (l1 l2 : Law.MagmaLaw α) : Ordering :=
  (compare l1.forks l2.forks).then <| (l1.cmpShape l2).then (l1.toList.cmp l2.toList)

/-- The largest used variable. -/
def FreeMagma.max : FreeMagma Nat → Nat
  | .Leaf i => i
  | .Fork l r => Nat.max l.max r.max

/-- The largest used variable. -/
def Law.MagmaLaw.max (l : Law.MagmaLaw Nat) : Nat := Nat.max l.lhs.max l.rhs.max

/-- Canonically reorders variables -/
def FreeMagma.canonicalize {α} [DecidableEq α] (m : FreeMagma α) : FreeMagma Nat :=
  (go m #[]).1
where
  go : FreeMagma α → Array α → FreeMagma Nat × Array α
  | .Leaf v, xs =>
    match xs.idxOf? v with
    | some i => (.Leaf i, xs)
    | none =>
      (.Leaf xs.size, xs.push v)
  | .Fork l r, xs =>
    let (l, xs) := go l xs
    let (r, xs) := go r xs
    (.Fork l r, xs)

def List.canonicalize {α} [DecidableEq α] (l : List α) : List Nat :=
  (go l []).1
where
  go : List α → List α → List Nat × List α
  | [], xs => ([], xs)
  | v :: l, xs =>
    match xs.idxOf? v with
    | some i => let (l', xs) := go l xs; (i::l', xs)
    | none => let (l', xs') := go l (xs ++ [v]); (xs.length :: l', xs')

/-- Canonically reorders variables -/
def Law.MagmaLaw.canonicalize {α} [DecidableEq α] (l : Law.MagmaLaw α) : Law.MagmaLaw Nat :=
  (go #[]).1
where
  go (arr : Array α) : Law.NatMagmaLaw × Array α :=
    let (lhs', arr) := FreeMagma.canonicalize.go l.lhs arr
    let (rhs', arr) := FreeMagma.canonicalize.go l.rhs arr
    (⟨lhs', rhs'⟩, arr)

/-- Checks whether variables are canonically ordered -/
def FreeMagma.isCanonical (next : Nat) : FreeMagma Nat → Option Nat
  | .Leaf i => do
    if i < next then
      return next
    else if i = next then
      return next + 1
    else
      none
  | .Fork l r => do (← l.isCanonical next) |> r.isCanonical

def Law.MagmaLaw.IsCanonicalLabel (l : Law.MagmaLaw Nat) : Prop :=
  ∃ n n', l.lhs.isCanonical 0 = some n ∧ l.rhs.isCanonical n = some n'

/--
Checks whether a magma law is canonical:
* Variables are canonically labeled
* `lhs < rhs` (with the exception of `0 ≃ 0`)
* The symmetric law did not come first
-/
def Law.MagmaLaw.IsCanonical (l : Law.MagmaLaw Nat) : Prop :=
  l.IsCanonicalLabel ∧
  (l.lhs.cmp l.rhs = .lt ∨ l.lhs = .Leaf 0) ∧
  l.symm.canonicalize.cmp l ≠ .lt

open Lean Qq

def TestNat (n : Nat) (P : Nat → Prop) : Prop := ∀ i < n, P i

theorem TestNat.succ {n P} (h1 : TestNat n P) (h2 : P n) : TestNat (n+1) P := sorry

def TestAllSplits (n : Nat) (P : Nat → Nat → Prop) : Prop := ∀ i j, i + j = n → P i j

def TestAllSplits' (i j : Nat) (P : Nat → Nat → Prop) : Prop :=
  ∀ i' < i, P i' (j + (i - i'))

theorem TestAllSplits'.succ {i j P}
    (h1 : TestAllSplits' i (j+1) P) (h2 : P i (j+1)) : TestAllSplits' (i+1) j P := sorry

def TestFreeMagmas (s n : Nat) (P : Nat → FreeMagma Nat → Prop) :=
  ∀ m n', m.forks = s → m.isCanonical n = some n' → P n' m

theorem TestFreeMagmas.succ {s n P}
    (H : TestAllSplits s fun s1 s2 =>
      TestFreeMagmas s1 n fun n l =>
        TestFreeMagmas s2 n fun n r =>
          P n (.Fork l r))
    : TestFreeMagmas (s+1) n P := sorry

def TestLawsBody (l r : FreeMagma Nat) (P : Law.NatMagmaLaw → Prop) :=
  l.cmp r = .lt ∨ l = Lf 0 →
  ¬(l ≃ r).symm.canonicalize.cmp (l ≃ r) = .lt → P (l ≃ r)

def TestLaws (s : Nat) (P : Law.NatMagmaLaw → Prop) :=
  ∀ l : Law.MagmaLaw Nat, l.forks = s → l.IsCanonical → P l

theorem TestLaws.mk {s P}
    (H : TestAllSplits s fun s1 s2 =>
    TestFreeMagmas s1 0 fun n l =>
      TestFreeMagmas s2 n fun _ r =>
        TestLawsBody l r P)
    : TestLaws s P := sorry

def TestLawsUpto (s : Nat) (P : Law.NatMagmaLaw → Prop) :=
  ∀ l : Law.MagmaLaw Nat, l.forks ≤ s → l.IsCanonical → P l

theorem TestLawsUpto.mk {s P}
    (H : TestNat (s+1) fun s' => TestLaws s' P)
    : TestLawsUpto s P := sorry

/--
This theorem demonstrates that `laws`, the list of laws considered in this project, indeed
contains all magma laws up to equivalence, up to 4 operations.
-/
theorem laws_complete' (l : Law.MagmaLaw Nat) (hl : l.forks ≤ 4) : ∃ (i : Nat), laws[i].iff l := sorry
