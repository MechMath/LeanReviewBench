import dep.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import dep.DifferentialGeometry.Tensor.RSTensor.Defs
open DifferentialGeometry.Tensor.Multilinear

noncomputable section

namespace DifferentialGeometry
namespace Tensor0SBundle

open Bundle Module
open scoped Manifold BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section ModelBasis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def coframeOfBasis (basis : Module.Basis Idx 𝕜 V) (i : Idx) : V →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap (basis.coord i)

omit [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem coframeOfBasis_apply (basis : Module.Basis Idx 𝕜 V) (i : Idx) (v : V) :
    coframeOfBasis basis i v = basis.coord i v  := by sorry

def continuousMultilinearMapBasisElem
    (basis : Module.Basis Idx 𝕜 V) (s : Nat) (slots : Fin s -> Idx) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => V) 𝕜 :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin s) (1 : 𝕜)).compContinuousLinearMap
    (fun a => coframeOfBasis basis (slots a))

omit [Fintype Idx] in
@[simp]
theorem continuousMultilinearMapBasisElem_apply
    (basis : Module.Basis Idx 𝕜 V) (s : Nat)
    (slots slots' : Fin s -> Idx) :
    continuousMultilinearMapBasisElem basis s slots (fun a => basis (slots' a)) =
      if slots = slots' then 1 else 0  := by sorry

omit [Fintype Idx] [DecidableEq Idx] in
theorem continuousMultilinearMapBasisElem_linearIndependent [Finite Idx]
    (basis : Module.Basis Idx 𝕜 V) (s : Nat) :
    LinearIndependent 𝕜 (continuousMultilinearMapBasisElem basis s)  := by sorry

def continuousMultilinearMapBasis
    (basis : Module.Basis Idx 𝕜 V) (s : Nat) :
    Module.Basis (Fin s -> Idx) 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => V) 𝕜) := by
  classical
  exact Module.Basis.mk (continuousMultilinearMapBasisElem_linearIndependent basis s)
    ((continuousMultilinearMapBasisElem_linearIndependent basis s).span_eq_top_of_card_eq_finrank'
      (by
        have hdim : Module.finrank 𝕜 V = Fintype.card Idx := by
          rw [Module.finrank_eq_card_basis basis]
        rw [Fintype.card_fun, Fintype.card_fin,
          finrank_continuousMultilinearMap (𝕜 := 𝕜) (F := V), hdim])).ge

omit [DecidableEq Idx] in
theorem continuousMultilinearMapBasis_apply
    (basis : Module.Basis Idx 𝕜 V) (s : Nat) (slots : Fin s -> Idx) :
    continuousMultilinearMapBasis basis s slots =
      continuousMultilinearMapBasisElem basis s slots  := by sorry

omit [DecidableEq Idx] in
theorem continuousMultilinearMapBasis_repr
    (basis : Module.Basis Idx 𝕜 V) (s : Nat)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => V) 𝕜)
    (slots : Fin s -> Idx) :
    (continuousMultilinearMapBasis basis s).repr A slots =
      A (fun a => basis (slots a))  := by sorry

end ModelBasis

section Tensor0S

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {s : Nat} {x : M}

def tensor0SBasis (basis : Module.Basis Idx 𝕜 (TangentSpace I x)) (s : Nat) :
    Module.Basis (Fin s -> Idx) 𝕜 (Tensor0SSpace s I x) :=
  continuousMultilinearMapBasis basis s

def basisTensor0S
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x)) (slots : Fin s -> Idx) :
    Tensor0SSpace s I x :=
  tensor0SBasis (I := I) basis s slots

def component0S
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) : 𝕜 :=
  A (fun a => basis (slots a))

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component0S_apply
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis A slots = A (fun a => basis (slots a))  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_congr_slots
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) {slots slots' : Fin s -> Idx}
    (h : slots = slots') :
    component0S (I := I) basis A slots = component0S (I := I) basis A slots'  := by sorry

omit [DecidableEq Idx] in
@[simp]
theorem tensor0SBasis_repr
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    (tensor0SBasis (I := I) basis s).repr A slots =
      component0S (I := I) basis A slots  := by sorry

def coordMap0S
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x)) (s : Nat) :
    Tensor0SSpace s I x →ₗ[𝕜] ((Fin s -> Idx) -> 𝕜) :=
  ((tensor0SBasis (I := I) basis s).equivFun).toLinearMap

omit [DecidableEq Idx] in
@[simp]
theorem coordMap0S_apply
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) :
    coordMap0S (I := I) basis s A = component0S (I := I) basis A  := by sorry

def coordEquiv0S
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x)) (s : Nat) :
    Tensor0SSpace s I x ≃ₗ[𝕜] ((Fin s -> Idx) -> 𝕜) :=
  (tensor0SBasis (I := I) basis s).equivFun

omit [DecidableEq Idx] in
@[simp]
theorem coordEquiv0S_apply
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) :
    coordEquiv0S (I := I) basis s A = component0S (I := I) basis A  := by sorry

omit [Fintype Idx] [DecidableEq Idx] in
theorem ext0S_basis [Finite Idx]
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    {A B : Tensor0SSpace s I x}
    (h : ∀ slots : Fin s -> Idx,
      component0S (I := I) basis A slots = component0S (I := I) basis B slots) :
    A = B  := by sorry

theorem basisTensor0S_component
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (slots slots' : Fin s -> Idx) :
    component0S (I := I) basis (basisTensor0S (I := I) basis slots) slots' =
      if slots = slots' then 1 else 0  := by sorry

end Tensor0S

end Tensor0SBundle
end DifferentialGeometry

