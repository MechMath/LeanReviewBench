module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Path
public import dep.FLT.DedekindDomain.AdicValuation
public import dep.FLT.DedekindDomain.IntegralClosure
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.Hacks.RightActionInstances
public import dep.FLT.Mathlib.Algebra.Algebra.Bilinear
public import dep.FLT.Mathlib.Algebra.Algebra.Hom
public import dep.FLT.Mathlib.Algebra.Algebra.Pi
public import dep.FLT.Mathlib.Algebra.Algebra.Tower
public import dep.FLT.Mathlib.Algebra.Module.Submodule.Basic
public import dep.FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
public import dep.FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import dep.FLT.Mathlib.Topology.Algebra.UniformRing

@[expose] public section

open scoped WithZero Valued TensorProduct

open Valuation.IsRankOneDiscrete WithZero

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

section assumptions

variable [IsIntegralClosure B A L] [FiniteDimensional K L]

end assumptions

variable [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

namespace IsDedekindDomain.HeightOneSpectrum

variable (v : HeightOneSpectrum A) {A B}

/--
If we have an AKLB set-up, and `w` is a valuation on `L` extending `v` on `K`,
then `σ v w` is the ring homomorphism from (K with valuation v) to (L with valuation w).
More precisely, by (K with valuation v) we mean the
type synonym `WithVal (HeightOneSpectrum.valuation K v)`, which is `K` equipped with
the instance `Valued K Γ₀` coming from `v`. In particular this type synonym has
a canonical valuation, topology, and uniform addive group structure. It is shown
that `σ v w` is continuous.
-/
local notation "σ" => fun v w => algebraMap (WithVal (HeightOneSpectrum.valuation K v))
    (WithVal (HeightOneSpectrum.valuation L w))

include K L in
lemma adicValued.continuous_algebraMap
   (w : HeightOneSpectrum B) (hvw : w.under A = v) :
    Continuous (σ v w) := sorry

namespace Extension

variable {v} (w : v.Extension B)

/-- The map `(R,v) → (S,w)` as a semialgebra map over `R → S` (which is the same map!). -/
@[simps!]
def _root_.WithVal.semialgebraMap {R S Γ₀ Γ₀' : Type*} [CommRing R]
    [CommRing S] [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']
    [Algebra R S] (v : Valuation R Γ₀) (w : Valuation S Γ₀') :
    WithVal v →ₛₐ[algebraMap R S] WithVal w where
  __ := algebraMap (WithVal v) (WithVal w)
  map_smul' r x := sorry

/-- If w of L divides v of K, `underSemialgHom v w pf` is the canonical map `Kᵥ → L_w` lying
above `K → L`. Here we actually use the type synonyms `WithVal K` and `WithVal L`. -/
noncomputable def adicCompletionSemialgHom :
    v.adicCompletion K →ₛₐ[algebraMap K L] w.1.adicCompletion L :=
  ((adicCompletion.algEquiv L w.1).symm.toAlgHom.toSemialgHom).comp <|
    (((WithVal.semialgebraMap (v.valuation K) (w.1.valuation L)).restrictScalars <|
        UniformSpace.Completion.mapSemialgHom _ <|
          adicValued.continuous_algebraMap K L v w.1 w.2).comp
      (adicCompletion.algEquiv K v).toAlgHom.toSemialgHom)

include v in
/-- The map K_v → L_w is continuous. -/
lemma adicCompletionSemialgHom_continuous : Continuous (w.adicCompletionSemialgHom K L) := sorry

include A B in
/-- The canonical map K_v → L_w sends 𝓞_v to 𝓞_w. -/
lemma adicCompletionSemialgHom_image_adicCompletionIntegers :
    w.adicCompletionSemialgHom K L '' (v.adicCompletionIntegers K) ⊆
      w.1.adicCompletionIntegers L := sorry

/-- The K_v-algebra structure on L_w when w | v. -/
noncomputable
instance : Algebra (v.adicCompletion K) (w.1.adicCompletion L) :=
  (w.adicCompletionSemialgHom K L).toAlgebra

/-- The K_v-action on L_w is continuous. -/
instance : ContinuousSMul (adicCompletion K v) (adicCompletion L w.1) := sorry

end Extension

namespace adicCompletion

variable (B)

/-- The canonical map `K_v → ∏_{w|v} L_w` extending K → L. -/
noncomputable def semialgHomPi :
    v.adicCompletion K →ₛₐ[algebraMap K L] ∀ w : v.Extension B, w.1.adicCompletion L :=
  Pi.semialgHom _ _ fun i ↦ i.adicCompletionSemialgHom K L

/-- The canonical ring homomorphism `L ⊗_K K_v → ∏_{w|v} L_w` as an `L`-algebra map. -/
noncomputable abbrev baseChange :
    L ⊗[K] adicCompletion K v →ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  (semialgHomPi K L B v).baseChangeOfAlgebraMap

section ModuleTopology

open WithZeroMulInt Valued in
-- Make (v.adicCompletion K) a normed field.
-- This exists for number fields in Mathlib, but not for general Dedekind Domains.
-- v.asIdeal.absNorm may be 0, so just use 2 as the base for the norm.
/-- The data of a rank 1 (ℝ-valued) valuation on K_v. -/
noncomputable local instance :
    Valuation.RankOne (Valued.v : Valuation (adicCompletion K v) ℤᵐ⁰) where
  hom' := (toNNReal (sorry : (2 : NNReal) ≠ 0)).comp
    (valueGroup₀_equiv_withZeroMulInt _).toMonoidWithZeroHom
  strictMono' := toNNReal_strictMono (sorry) |>.comp
    (sorry)
  exists_val_nontrivial := sorry

open scoped TensorProduct.RightActions in
/-- ∏_{w|v} L_w is a finite K_v-module. -/
instance [FiniteDimensional K L] :
    Module.Finite (adicCompletion K v) (Π w : v.Extension B, w.1.adicCompletion L) := sorry

/-- L_w is a finite K_v-module if w | v. -/
instance [FiniteDimensional K L] (w : v.Extension B) :
    Module.Finite (adicCompletion K v) (adicCompletion L w.1) := sorry

include v in
/-- L_w has the K_v-module topology. -/
instance instIsModuleTopology [FiniteDimensional K L] (w : v.Extension B) :
    IsModuleTopology (v.adicCompletion K) (w.1.adicCompletion L) := sorry

include A v in
/-- ∏_{w|v} L_w has the K_v-module topology. -/
instance instIsModuleTopologyPi [FiniteDimensional K L] :
    -- the claim that L_w has the module topology.
    IsModuleTopology (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) := sorry

end ModuleTopology

end adicCompletion

section ModuleTopology

open Extension adicCompletion

variable (B)

/-- The canonical B-algebra map `B ⊗[A] 𝓞_v → L ⊗[K] K_v` -/
noncomputable def tensorAdicCompletionIntegersTo :
    B ⊗[A] adicCompletionIntegers K v →ₐ[B] L ⊗[K] adicCompletion K v :=
  Algebra.TensorProduct.lift
    (Algebra.algHom _ _ _)
    ((Algebra.TensorProduct.includeRight.restrictScalars A).comp (IsScalarTower.toAlgHom _ _ _))
    (fun _ _ ↦ .all _ _)

instance : MulActionHomClass
    (L ⊗[K] adicCompletion K v →ₐ[L] (w : Extension B v) → adicCompletion L w.1) B
    (L ⊗[K] adicCompletion K v) ((w : Extension B v) → adicCompletion L w.1) := sorry

namespace Extension

variable {B} (w : v.Extension B)

/-- The restriction of `adicCompletionSemialgHom` to a map `𝓞_v → 𝓞_w`. -/
noncomputable def adicCompletionIntegersRingHom :
    v.adicCompletionIntegers K →+* w.1.adicCompletionIntegers L :=
  RingHom.restrict (w.adicCompletionSemialgHom K L) _ _
    fun x hx ↦ w.adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨x, hx, rfl⟩

/-- If `w` is an extension of `v`, then `𝓞_w` is naturally an `𝓞_v`-algebra. -/
noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  (w.adicCompletionIntegersRingHom K L).toAlgebra

variable {v} in
/-- If `w` is an extension of `v`, then `L_w` is naturally an `𝓞_v`-algebra. -/
noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletion L) :=
  Algebra.compHom (w.1.adicCompletion L) (algebraMap _ (adicCompletion K v))

end Extension

open scoped TensorProduct.RightActions in
instance : IsBiscalar B (v.adicCompletionIntegers K) (tensorAdicCompletionIntegersTo K L B v) := sorry

instance {w : v.Extension B} : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v)
    (w.1.adicCompletion L) := sorry

namespace Extension

variable (w : v.Extension B)

/-- A shortcut instance for the action of `𝓞ᵥ` on `Kᵥ`. -/
noncomputable local instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  LieAlgebra.ofAssociativeAlgebra.toMulAction

open scoped TensorProduct.RightActions in
/-- `𝓞_w` is finite over `𝓞_v`. -/
-- This can be proved for finite extensions of complete discretely valued fields without
-- reference to underlying fields being completed, but this is sufficient for our
-- purposes.
noncomputable instance (priority := 1001) [Module.Finite A B] [FiniteDimensional K L] :
    Module.Finite (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := sorry

end Extension

end ModuleTopology

namespace adicCompletion

open Extension

section RamificationInertia

variable {v} (w : v.Extension B)

end RamificationInertia

variable [FiniteDimensional K L] [Module.Finite A B] (B)

variable (v : HeightOneSpectrum A) (w : v.Extension B)

end adicCompletion

namespace adicCompletionIntegers

open adicCompletion

variable (B)

end adicCompletionIntegers

namespace adicCompletion

open Extension

variable [FiniteDimensional K L] [Module.Finite A B]

end IsDedekindDomain.HeightOneSpectrum.adicCompletion
