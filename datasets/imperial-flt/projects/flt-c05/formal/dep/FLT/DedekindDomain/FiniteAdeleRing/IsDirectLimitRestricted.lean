module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import dep.FLT.Mathlib.Algebra.IsDirectLimit
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic

@[expose] public section

namespace RestrictedProduct

open Set Filter

section directedSystem

variable {ι : Type*} {𝓕 : Filter ι}

instance : Nonempty 𝓕.setsᵒᵈ := sorry

variable {R : ι → Type*} {A : ι → Type*} [Π i, SetLike (A i) (R i)] {C : Π i, A i}

instance instDirectedSystem :
    DirectedSystem (fun (S : 𝓕.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
      (fun _ _ h ↦ RestrictedProduct.inclusion _ _ <| monotone_principal h) := sorry

end directedSystem

section inclusion

open scoped RestrictedProduct TensorProduct IsDirectLimit

variable {A : Type*} [CommRing A] {ι : Type*} {R : ι → Type*} {ℱ : Filter ι}
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)} {M : Type*}
  [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] (S : ℱ.setsᵒᵈ)

open Set Filter RestrictedProduct

instance : DirectedSystem (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
    fun _ _ h ↦ (inclusionLinearMap A R C <| monotone_principal h) := sorry

instance directed : IsDirected (ℱ.setsᵒᵈ) (· ≤ ·) := sorry

end inclusion

variable {ι : Type*} (R : ι → Type*) {ℱ : Filter ι} (A : Type*) [CommRing A]

variable [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}

instance {I : Type*} [Preorder I] (𝓖 : I → Filter ι) (h𝓖 : Antitone 𝓖) :
    DirectedSystem (fun x ↦ Πʳ (i : ι), [R i, ↑(C i)]_[𝓖 x])
      (inclusionLinearMap A R C <| @h𝓖 · · ·) := sorry

instance instIsDirectLimit {I : Type*} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (𝓖 : I → Filter ι) (h𝓖 : Antitone 𝓖) (hℱ : ℱ = iInf 𝓖) :
    IsDirectLimit (inclusionLinearMap A R C <| @h𝓖 · · ·)
    (inclusionLinearMap A R C <| hℱ.trans_le <| iInf_le 𝓖 ·) := sorry

instance instIsDirectLimit' : IsDirectLimit (M := fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
    ((fun _ _ h ↦ inclusionLinearMap A R C <| monotone_principal h))
    (fun S ↦ inclusionLinearMap A R C <| Filter.le_principal_iff.2 S.2) := sorry

end RestrictedProduct
