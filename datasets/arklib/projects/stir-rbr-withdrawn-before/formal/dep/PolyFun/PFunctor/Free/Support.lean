module

public import Batteries.Tactic.Lint
public import Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Init
public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor
public import Mathlib.Util.Notation3
public import dep.PolyFun.Control.Monad.Hom
public import dep.PolyFun.Control.Monad.Support
public import dep.PolyFun.Control.Monad.Support.Instances
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Free.Displayed
public import dep.PolyFun.PFunctor.Free.Path
public import dep.PolyFun.PFunctor.Lens.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.ToCslib.Data.PFunctor.Free.Basic
public import dep.dep.CslibCompat.Basic
public import dep.dep.CslibCompat.Free

@[expose] public section

universe uA uB v w

namespace PFunctor.FreeM

open MonadAttach

variable {P : PFunctor.{uA, uB}} {α β : Type v}

/-- The structural support of a free tree: every direction of every operation node is
possible. -/
def supp : FreeM P α → Set α
  | .pure a => {a}
  | .liftBind _ r => ⋃ b, supp (r b)

/-- Reachability at a child is reachability at the node. -/
theorem mem_supp_liftBind_of_mem {op : P.A} {r : P.B op → FreeM P α} {b : P.B op} {a : α}
    (h : a ∈ supp (r b)) : a ∈ supp (FreeM.liftBind op r) := sorry

/-- Attach the structural-support proof to every leaf, by structural recursion. -/
def attachSupp : (x : FreeM P α) → FreeM P {a : α // a ∈ supp x}
  | .pure a => .pure ⟨a, rfl⟩
  | .liftBind op r => .liftBind op fun b =>
      FreeM.map (fun z => ⟨z.1, mem_supp_liftBind_of_mem z.2⟩) (attachSupp (r b))

instance instMonadAttach : MonadAttach (FreeM P) where
  CanReturn x a := a ∈ supp x
  attach := attachSupp

/-- The structural support is the strongest postcondition: anything reachable in a tree of
refined values satisfies the refinement. -/
theorem supp_map_imp {Q : α → Prop} (x : FreeM P {a : α // Q a}) {b : α} :
    b ∈ supp (Subtype.val <$> x) → Q b := sorry

@[deprecated (since := "2026-10-19")] alias supp_map := supp_map_imp

instance instExactMonadAttach : ExactMonadAttach (FreeM P) := sorry

end PFunctor.FreeM
