module

public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import dep.FLT.AutomorphicForm.GroupTheoryStuff

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true

/-- Mapping double cosets across `MonoidHom`s. -/
def DoubleCoset.map {G₁ G₂ : Type*} [Group G₁] [Group G₂] (H₁ K₁ : Subgroup G₁)
    (H₂ K₂ : Subgroup G₂) (e : G₁ →* G₂) (eH : H₁ ≤ H₂.comap e) (eK : K₁ ≤ K₂.comap e) :
    DoubleCoset.Quotient (G := G₁) H₁ K₁ → DoubleCoset.Quotient (G := G₂) H₂ K₂ :=
  Quotient.map e fun a b H ↦ sorry

variable {G : Type*} [Group G] (H K : Subgroup G)

local notation H "＼" G "／" K:max => DoubleCoset.Quotient (G := G) H K

local notation H "﹨" G:max => _root_.Quotient (QuotientGroup.rightRel (α := G) H)

lemma DoubleCoset.σ_exists :
    ∃ (σ : H＼G／K → G) (x : G → H) (y : G → K),
    (∀ a, a = x a * σ (DoubleCoset.mk H K a) * y a) ∧
    (∀ a, x (σ a) = 1) ∧ (∀ a, y (σ a) = 1) ∧ (σ (mk H K 1) = 1) ∧
    (∀ a, ∀ k : K, x (a * k) = x a) := sorry

variable {H K} in
/-- An arbitrary section of `G → H＼G／K`. -/
noncomputable def DoubleCoset.σ (g : H＼G／K) : G := (DoubleCoset.σ_exists H K).choose g
