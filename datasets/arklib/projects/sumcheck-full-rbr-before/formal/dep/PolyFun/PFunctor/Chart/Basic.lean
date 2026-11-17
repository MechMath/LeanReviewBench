module

public import Batteries.Tactic.Lint
public import Cslib.Init
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Util.Notation3
public import dep.PolyFun.PFunctor.Basic
public import dep.PolyFun.PFunctor.Equiv.Basic
public import dep.PolyFun.PFunctor.Obj
public import dep.dep.CslibCompat.Basic

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆

namespace PFunctor

namespace Chart

@[ext (iff := false)]
theorem ext {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (c₁ c₂ : Chart P Q)
    (h₁ : ∀ a, c₁.toFunA a = c₂.toFunA a) (h₂ : ∀ a, c₁.toFunB a = (h₁ a) ▸ c₂.toFunB a) :
    c₁ = c₂ := sorry

/-- The identity chart -/
protected def id (P : PFunctor.{uA, uB}) : Chart P P := id ⇉ fun _ => id

/-- Composition of charts -/
def comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (c' : Chart Q R) (c : Chart P Q) : Chart P R where
  toFunA := c'.toFunA ∘ c.toFunA
  toFunB := fun i => c'.toFunB (c.toFunA i) ∘ c.toFunB i

/-- Infix notation for chart composition `c' ∘c c`; activate it with `open scoped PFunctor`. -/
scoped[PFunctor] infixl:75 " ∘c " => PFunctor.Chart.comp

/-- An equivalence between two polynomial functors `P` and `Q`, using charts.
    This corresponds to an isomorphism in the category `PFunctor` with `Chart` morphisms. -/
@[ext]
protected structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward chart of the equivalence, from `P` to `Q`. -/
  toChart : Chart P Q
  /-- The backward chart of the equivalence, from `Q` to `P`. -/
  invChart : Chart Q P
  left_inv : comp invChart toChart = Chart.id P := by simp
  right_inv : comp toChart invChart = Chart.id Q := by simp

/-- Infix notation for chart equivalence `P ≃c Q`; activate it with `open scoped PFunctor`. -/
scoped[PFunctor] infix:50 " ≃c " => PFunctor.Chart.Equiv

namespace Equiv

/-- The identity equivalence on `P`, built from the identity chart in both directions. -/
@[refl, simps]
def refl (P : PFunctor.{uA, uB}) : P ≃c P :=
  ⟨Chart.id P, Chart.id P, rfl, rfl⟩

/-- The inverse equivalence, swapping the forward and backward charts of `e`. -/
@[symm, simps]
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : P ≃c Q) : Q ≃c P :=
  ⟨e.invChart, e.toChart, e.right_inv, e.left_inv⟩

/-- The composite equivalence `P ≃c R` obtained by chaining `e₁ : P ≃c Q` and `e₂ : Q ≃c R`. -/
@[trans, simps]
def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (e₁ : P ≃c Q) (e₂ : Q ≃c R) : P ≃c R :=
  ⟨e₂.toChart ∘c e₁.toChart, e₁.invChart ∘c e₂.invChart,
    sorry,
    sorry⟩

/-- Chart equivalences compose in `calc` chains, across independent universes. -/
instance instTrans :
    @Trans PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{uA₃, uB₃}
      Chart.Equiv Chart.Equiv Chart.Equiv where
  trans := Equiv.trans

section Groupoid

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {S : PFunctor.{uA₄, uB₄}}

end Groupoid

end Equiv

/-- The (unique) terminal chart from any functor `P` to `y = y`.

`y` is the terminal object of the chart category — a single position with a
single direction — corresponding to the identity arrow `1 → 1` in `Set^→`.
This differs from the lens-side terminal `1` (positions `1`, no directions). -/
def terminal {P : PFunctor.{uA, uB}} : Chart P y :=
  (fun _ => PUnit.unit) ⇉ (fun _ _ => PUnit.unit)

@[deprecated (since := "2026-10-19")] alias toOne := terminal

/-- Left injection chart `inl : P → P + Q`. -/
def inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Chart.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q) :=
  Sum.inl ⇉ fun _ => id

/-- Right injection chart `inr : Q → P + Q`. -/
def inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Chart.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q) :=
  Sum.inr ⇉ fun _ => id

/-- Copairing of charts `[c₁, c₂]c : P + Q → R`. -/
def sumPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB₃}}
    (c₁ : Chart P R) (c₂ : Chart Q R) :
    Chart.{max uA₁ uA₂, uB, uA₃, uB₃} (P + Q) R :=
  Sum.elim c₁.toFunA c₂.toFunA ⇉ fun
    | .inl pa => c₁.toFunB pa
    | .inr qa => c₂.toFunB qa

/-- Parallel application of charts for coproduct `c₁ ⊎c c₂ : P + Q → R + W`. -/
def sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₃}} (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.{max uA₁ uA₂, uB₁, max uA₃ uA₄, uB₃} (P + Q) (R + W) :=
  Sum.map c₁.toFunA c₂.toFunA ⇉ fun
    | .inl pa => c₁.toFunB pa
    | .inr qa => c₂.toFunB qa

/-- Projection chart `fst : P ⊗ Q → P`. -/
def fst {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P ⊗ Q) P :=
  Prod.fst ⇉ (fun _ => Prod.fst)

/-- Projection chart `snd : P ⊗ Q → Q`. -/
def snd {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, uA₂, uB₂} (P ⊗ Q) Q :=
  Prod.snd ⇉ (fun _ => Prod.snd)

/-- Pairing of charts `⟨c₁, c₂⟩c : P → Q ⊗ R`. -/
def tensorPair {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (c₁ : Chart P Q) (c₂ : Chart P R) :
    Chart.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q ⊗ R) :=
  (fun pa => (c₁.toFunA pa, c₂.toFunA pa)) ⇉
    (fun pa pb => (c₁.toFunB pa pb, c₂.toFunB pa pb))

/-- Parallel application of charts for tensor `c₁ ⊗c c₂ : P ⊗ Q → R ⊗ W`. -/
def tensorMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P ⊗ Q) (R ⊗ W) :=
  Prod.map c₁.toFunA c₂.toFunA ⇉
    fun (pa, qa) => Prod.map (c₁.toFunB pa) (c₂.toFunB qa)

/-- Parallel application of charts for polynomial product `c₁ ×c c₂ : P * Q → R * W`. -/
def prodMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P * Q) (R * W) :=
  Prod.map c₁.toFunA c₂.toFunA ⇉
    fun (pa, qa) => Sum.map (c₁.toFunB pa) (c₂.toFunB qa)

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

set_option linter.checkUnivs false in
/-- The type of charts from a polynomial functor `P` to `y`.

A chart `P → y` is equivalent to a function `(a : P.A) → P.B a → PUnit`,
i.e. a boundary valuation that picks out a single direction at every
position. It is the chart analogue of the lens sections `PFunctor.Section`. -/
-- `Chart.Enclose`'s two universe pairs are the independent domain (`uA`/`uB`) and
-- codomain (`uA₁`/`uB₁`) position/direction universes, kept independent.
def Enclose (P : PFunctor.{uA, uB}) : Type max uA uA₁ uB uB₁ :=
  Chart P y.{uA₁, uB₁}

set_option linter.checkUnivs false in
-- The alias keeps `Chart.Enclose`'s independent codomain universes `uA₁`/`uB₁`.
@[deprecated (since := "2026-10-19")] alias enclose := Enclose

@[inherit_doc] scoped[PFunctor] infixl:75 " ⊎c " => PFunctor.Chart.sumMap

@[inherit_doc] scoped[PFunctor] infixl:75 " ⊗c " => PFunctor.Chart.tensorMap

@[inherit_doc] scoped[PFunctor] infixl:75 " ×c " => PFunctor.Chart.prodMap

/-- Notation for the copairing `sumPair c₁ c₂` of two charts out of a sum; activate it with
`open scoped PFunctor.Chart`. -/
scoped notation "[" c₁ "," c₂ "]c" => sumPair c₁ c₂

/-- Notation for the pairing `tensorPair c₁ c₂` of two charts into a tensor; activate it with
`open scoped PFunctor.Chart`. -/
scoped notation "⟨" c₁ "," c₂ "⟩c" => tensorPair c₁ c₂

section Sum

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
  {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}} {S : PFunctor.{uA₅, uB₅}}

namespace Equiv

variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}

end Equiv

end Sum

section Tensor

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {W : PFunctor.{uA₄, uB₄}} {S : PFunctor.{uA₅, uB₅}}

namespace Equiv

/-- Tensor product with `y` is identity (right) -/
def tensorY : P ⊗ y ≃c P where
  toChart := Prod.fst ⇉ (fun _ => Prod.fst)
  invChart := (fun p => (p, PUnit.unit)) ⇉ (fun _ b => (b, PUnit.unit))
  left_inv := rfl
  right_inv := rfl

/-- Tensor product with `y` is identity (left) -/
def yTensor : y ⊗ P ≃c P where
  toChart := Prod.snd ⇉ (fun _ => Prod.snd)
  invChart := (fun p => (PUnit.unit, p)) ⇉ (fun _ b => (PUnit.unit, b))
  left_inv := rfl
  right_inv := rfl

@[deprecated (since := "2026-08-17")] alias tensorX := tensorY

@[deprecated (since := "2026-08-17")] alias xTensor := yTensor

end Equiv

end Tensor

section Prod

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {W : PFunctor.{uA₄, uB₄}}

namespace Equiv

end Equiv

end Prod

namespace Equiv

/-- ULift equivalence for charts. -/
def ulift {P : PFunctor.{uA, uB}} : P.ulift ≃c P where
  toChart := (fun a => ULift.down a) ⇉ (fun _ b => ULift.down b)
  invChart := (fun a => ULift.up a) ⇉ (fun _ b => ULift.up b)
  left_inv := rfl
  right_inv := rfl

end Equiv

end Chart

namespace Equiv

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}

/-- Convert an equivalence between two polynomial functors `P` and `Q` to a chart. -/
def toChart (e : P ≃ₚ Q) : Chart P Q where
  toFunA := e.equivA
  toFunB := fun a => e.equivB a

@[simp]
theorem symm_toChart_comp_toChart (e : P ≃ₚ Q) :
    e.symm.toChart ∘c e.toChart = Chart.id P := sorry

@[simp]
theorem toChart_comp_symm_toChart (e : P ≃ₚ Q) :
    e.toChart ∘c e.symm.toChart = Chart.id Q := sorry

/-- Convert an equivalence between two polynomial functors to a chart equivalence.

Chart-side analogue of `Equiv.toLensEquiv`. Together with `Chart.Equiv.refl`,
`symm`, and `trans`, this establishes a faithful functor
`PFunctor.Equiv → Chart.Equiv`. -/
def toChartEquiv (e : P ≃ₚ Q) : P ≃c Q where
  toChart := e.toChart
  invChart := e.symm.toChart
  left_inv := symm_toChart_comp_toChart e
  right_inv := toChart_comp_symm_toChart e

end Equiv

namespace Chart.Equiv

variable {I : Type v}

/-- Sigma of an empty family is the zero functor. -/
def emptySigma [IsEmpty I] {F : I → PFunctor.{uA, uB}} : sigma F ≃c 0 :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.emptySigma (F := F))

@[deprecated (since := "2026-10-19")] alias sigmaEmpty := emptySigma

/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself
    (up to `ulift`). -/
def punitSigma {F : PUnit → PFunctor.{uA, uB}} : sigma F ≃c (F PUnit.unit).ulift :=
  PFunctor.Equiv.toChartEquiv
    (PFunctor.Equiv.trans
      (PFunctor.Equiv.punitSigma (F := F))
      (PFunctor.Equiv.ulift (F PUnit.unit)).symm)

@[deprecated (since := "2026-10-19")] alias sigmaUnit := punitSigma

/-- Sigma of a unique-indexed family is equivalent to the default fiber
    (up to `ulift`). -/
def uniqueSigma [Unique I] {F : I → PFunctor.{uA, uB}} : sigma F ≃c (F default).ulift :=
  PFunctor.Equiv.toChartEquiv
    (PFunctor.Equiv.trans
      (PFunctor.Equiv.uniqueSigma (F := F))
      (PFunctor.Equiv.ulift (F default)).symm)

@[deprecated (since := "2026-10-19")] alias sigmaOfUnique := uniqueSigma

/-- Left distributivity of polynomial product over sigma. -/
def prodSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂ v, max uB₁ uB₂, max uA₁ uA₂ v, max uB₁ uB₂}
      (P * sigma F) (sigma (fun i => (P * F i : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}))) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.prodSigmaDistrib (P := P) (F := F))

/-- Right distributivity of polynomial product over sigma. -/
def sigmaProdDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂ v, max uB₁ uB₂, max uA₁ uA₂ v, max uB₁ uB₂}
      (sigma F * P) (sigma (fun i => (F i * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}))) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.sigmaProdDistrib (P := P) (F := F))

/-- Left distributivity of tensor product over sigma. -/
def tensorSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    P ⊗ sigma F ≃c sigma (fun i => P ⊗ F i) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.tensorSigmaDistrib (P := P) (F := F))

/-- Right distributivity of tensor product over sigma. -/
def sigmaTensorDistrib {P : PFunctor.{uA₂, uB₂}} {F : I → PFunctor.{uA₁, uB₁}} :
    sigma F ⊗ P ≃c sigma (fun i => F i ⊗ P) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.sigmaTensorDistrib (F := F) (P := P))

/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def piPUnit {P : PFunctor.{uA, uB}} : pi (fun (_ : PUnit) => P) ≃c P where
  toChart := (fun f => f PUnit.unit) ⇉ (fun _ s => s.2)
  invChart := (fun pa _ => pa) ⇉ (fun _ pb => ⟨PUnit.unit, pb⟩)
  left_inv := sorry
  right_inv := sorry

@[deprecated (since := "2026-10-19")] alias piUnit := piPUnit

/-- Pi of a family of zero functors over an inhabited type is the zero functor. -/
def piZero [Inhabited I] {F : I → PFunctor.{uA, uB}} (F_zero : ∀ i, F i = 0) :
    pi F ≃c 0 := by
  have : IsEmpty (pi F).A := by
    refine ⟨fun f => ?_⟩
    have hf : (F default).A := f default
    rw [F_zero (default : I)] at hf
    exact hf.elim
  refine
    { toChart := isEmptyElim ⇉ fun a => isEmptyElim a
      invChart := PEmpty.elim ⇉ fun a => PEmpty.elim a
      left_inv := sorry
      right_inv := sorry }

end Chart.Equiv

end PFunctor
