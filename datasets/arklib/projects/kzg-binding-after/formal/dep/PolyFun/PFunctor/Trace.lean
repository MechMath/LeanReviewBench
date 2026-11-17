module

public import Batteries.Tactic.Lint
public import Cslib.Init
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.Control.Trace
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Chart.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic

@[expose] public section

universe uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ v w

namespace PFunctor

attribute [local implicit_reducible] PFunctor.Idx

/--
The free monoid on `P`-events.  Definitionally `FreeMonoid (Idx P)`, which
in turn is reducibly `List (Idx P)`.  This is the universal carrier for
"finite ordered logs of `P`-events".
-/
abbrev TraceList (P : PFunctor.{uA, uB}) : Type max uA uB :=
  FreeMonoid (Idx P)

namespace TraceList

/-- Relabel-and-filter the events of a trace list along a partial map of
indices: `List.filterMap` with the monoid structure of `TraceList` made
explicit. `Trace.mapPartial` is this operation pointwise. -/
def mapPartial {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    (f : Idx P → Option (Idx Q)) (t : TraceList P) : TraceList Q :=
  FreeMonoid.ofList (t.toList.filterMap f)

/-- Partial event maps compose by binding their optional outputs. -/
theorem mapPartial_mapPartial {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
    {R : PFunctor.{uA₃, uB₃}} (g : Idx Q → Option (Idx R))
    (f : Idx P → Option (Idx Q)) (t : TraceList P) :
    mapPartial g (mapPartial f t) = mapPartial (fun i => (f i).bind g) t := sorry

@[deprecated (since := "2026-10-19")] alias mapPartial_comp := mapPartial_mapPartial

end TraceList

/--
An `X`-indexed trace of `P`-events: for each input `x : X`, a finite ordered
list of `P`-events.  Specialisation of `Control.Trace` at
`ω = TraceList P`, inheriting a pointwise monoid structure.
-/
abbrev Trace (P : PFunctor.{uA, uB}) (X : Type v) : Type max uA uB v :=
  Control.Trace (TraceList P) X

namespace Trace

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}
  {R : PFunctor.{uA₃, uB₃}} {X Y : Type v}

/--
Relabel-and-filter a trace along a partial map of indices.  This is the
single primitive for moving traces between polynomial functors: total chart
pushforward and summand restriction are both specialisations of it.
-/
def mapPartial (f : Idx P → Option (Idx Q)) (t : Trace P X) : Trace Q X :=
  fun x => TraceList.mapPartial f (t x)

theorem mapPartial_mapPartial (g : Idx Q → Option (Idx R)) (f : Idx P → Option (Idx Q))
    (t : Trace P X) :
    mapPartial g (mapPartial f t) = mapPartial (fun i => (f i).bind g) t := sorry

@[deprecated (since := "2026-10-19")] alias mapPartial_comp := mapPartial_mapPartial

end Trace

namespace Trace

variable {P Q : PFunctor.{uA, uB}} {X : Type v}

end Trace

end PFunctor
