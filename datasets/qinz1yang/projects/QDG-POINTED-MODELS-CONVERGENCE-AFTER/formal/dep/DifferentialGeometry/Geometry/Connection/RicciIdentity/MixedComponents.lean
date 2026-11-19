import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Basic
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ApplyInput
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ModelBridge
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Formula
import dep.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.RankOneTwo
import dep.DifferentialGeometry.Tensor.Contraction.ProductRules
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor.RicciIdentity

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Contraction (contractUpper
  contractUpper_commutator_of_second_product_rules contractUpper_second_product_of_first_product_rules)
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section MixedComponentAlgebra

def deltaMulti {Idx : Type*} {r : ℕ} [DecidableEq Idx]
    (L A : Fin r -> Idx) : Real :=
  if A = L then 1 else 0

def covariantCurvAction {Idx : Type*} [Fintype Idx] {n : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (A : (Fin n -> Idx) -> Real) (K : Fin n -> Idx) : Real :=
  -∑ q : Fin n, ∑ m : Idx,
    R i j m (K q) * A (Function.update K q m)

theorem contractUpper_components_eq_component_applyInput
    {Idx : Type*} [Fintype Idx] {r s : ℕ} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (T : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s x)
    (theta :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r x)
    (K : Fin s -> Idx) :
    contractUpper
        (fun L : Fin r -> Idx => component0S (I := I) basis theta L)
        (fun L : Fin r -> Idx => fun K : Fin s -> Idx =>
          componentRSField (I := I) basis T L K) K =
      component0S (I := I) basis (T theta) K  := by sorry

@[simp] theorem deltaMulti_self {Idx : Type*} {r : ℕ} [DecidableEq Idx]
    (L : Fin r -> Idx) :
    deltaMulti L L = 1  := by sorry

theorem deltaMulti_eq_zero_of_ne {Idx : Type*} {r : ℕ} [DecidableEq Idx]
    {L A : Fin r -> Idx} (h : A ≠ L) :
    deltaMulti L A = 0  := by sorry

@[simp] theorem contractUpper_deltaMulti {Idx : Type*}
    [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (L : Fin r -> Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) :
    contractUpper (deltaMulti L) beta K = beta L K  := by sorry

private lemma deltaMulti_update_eq_one_iff {Idx : Type*}
    [DecidableEq Idx] {r : ℕ}
    (L A : Fin r -> Idx) (p : Fin r) (m : Idx) :
    deltaMulti L (Function.update A p m) = 1 ↔
      Function.update A p m = L  := by sorry

private lemma update_eq_of_update_eq {Idx : Type*}
    {r : ℕ}
    {L A : Fin r -> Idx} {p : Fin r} {m : Idx}
    (h : Function.update A p m = L) :
    A = Function.update L p (A p)  := by sorry

private lemma update_value_eq_of_update_eq {Idx : Type*}
    {r : ℕ}
    {L A : Fin r -> Idx} {p : Fin r} {m : Idx}
    (h : Function.update A p m = L) :
    m = L p  := by sorry

private lemma update_update_same_apply {Idx : Type*}
    {r : ℕ}
    (L : Fin r -> Idx) (p : Fin r) (m : Idx) :
    Function.update (Function.update L p m) p (L p) = L  := by sorry

private def updateSwapEquiv {Idx : Type*} {r : ℕ}
    (p : Fin r) : ((Fin r -> Idx) × Idx) ≃ ((Fin r -> Idx) × Idx) where
  toFun Am := (Function.update Am.1 p Am.2, Am.1 p)
  invFun Am := (Function.update Am.1 p Am.2, Am.1 p)
  left_inv := by
    intro Am
    cases Am with
    | mk A m =>
        ext q <;> simp
  right_inv := by
    intro Am
    cases Am with
    | mk A m =>
        ext q <;> simp

private lemma sum_delta_update_pair {Idx : Type*}
    [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (L : Fin r -> Idx) (p : Fin r)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) :
    (∑ A : Fin r -> Idx, ∑ m : Idx,
      R i j m (A p) * deltaMulti L (Function.update A p m) * beta A K)
      =
    ∑ m : Idx, R i j (L p) m *
      beta (Function.update L p m) K  := by sorry

private lemma contractUpper_covariantCurvAction_deltaMulti
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (L : Fin r -> Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) :
    contractUpper (covariantCurvAction R i j (deltaMulti L)) beta K =
      -∑ p : Fin r, ∑ m : Idx,
        R i j (L p) m * beta (Function.update L p m) K  := by sorry

theorem contract_covariantCurvAction_deltaMulti_eq_mixedCurvAction
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (L : Fin r -> Idx) (K : Fin s -> Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real) :
    covariantCurvAction R i j
        (contractUpper (deltaMulti L) beta) K -
      contractUpper
        (covariantCurvAction R i j (deltaMulti L)) beta K
      =
        (∑ p : Fin r, ∑ m : Idx,
          R i j (L p) m * beta (Function.update L p m) K) -
        (∑ q : Fin s, ∑ m : Idx,
          R i j m (K q) * beta L (Function.update K q m))  := by sorry

def mixedCurvAction {Idx : Type*} [Fintype Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (L : Fin r -> Idx) (K : Fin s -> Idx) : Real :=
  (∑ p : Fin r, ∑ m : Idx,
    R i j (L p) m * beta (Function.update L p m) K) -
  (∑ q : Fin s, ∑ m : Idx,
    R i j m (K q) * beta L (Function.update K q m))

def MixedRicciIdentityCoord {Idx : Type*} [Fintype Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real) : Prop :=
  ∀ L K, commBeta L K = mixedCurvAction R i j beta L K

theorem mixedRicciIdentityCoord_of_contract_probe_identities
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commContract : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commProbe : (Fin r -> Idx) -> (Fin r -> Idx) -> Real)
    (hcontract : ∀ L K,
      contractUpper (deltaMulti L) commBeta K =
        commContract L K - contractUpper (commProbe L) beta K)
    (hcontractCov : ∀ L K,
      commContract L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K)
    (hprobeCov : ∀ L A,
      commProbe L A = covariantCurvAction R i j (deltaMulti L) A) :
    MixedRicciIdentityCoord R i j commBeta beta  := by sorry

theorem mixedRicciIdentityCoord_of_second_product_identities
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta beta_i beta_j beta_ij beta_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commContract contract_ij contract_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commProbe probe_i probe_j probe_ij probe_ji :
      (Fin r -> Idx) -> (Fin r -> Idx) -> Real)
    (hcommBeta : ∀ L K, commBeta L K = beta_ij L K - beta_ji L K)
    (hcommContract : ∀ L K, commContract L K = contract_ij L K - contract_ji L K)
    (hcommProbe : ∀ L A, commProbe L A = probe_ij L A - probe_ji L A)
    (hprod_ij : ∀ L K,
      contract_ij L K =
        contractUpper (probe_ij L) beta K +
          contractUpper (probe_j L) beta_i K +
          contractUpper (probe_i L) beta_j K +
          contractUpper (deltaMulti L) beta_ij K)
    (hprod_ji : ∀ L K,
      contract_ji L K =
        contractUpper (probe_ji L) beta K +
          contractUpper (probe_i L) beta_j K +
          contractUpper (probe_j L) beta_i K +
          contractUpper (deltaMulti L) beta_ji K)
    (hcontractCov : ∀ L K,
      commContract L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K)
    (hprobeCov : ∀ L A,
      commProbe L A = covariantCurvAction R i j (deltaMulti L) A) :
    MixedRicciIdentityCoord R i j commBeta beta  := by sorry

omit [IsManifold I ∞ M] in
theorem coordDeriv_applyInput_eq_contractUpper
    [IsManifold I 1 M]
    [IsManifold I (∞ : WithTop ℕ∞) M]
    {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (theta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (x₀ : M) (K : Fin s -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I) (fun x => X x) x₀
        (fun y : M =>
          tensorRSFieldApplyInput (𝕜 := Real) (E := E) (H := H) (I := I)
            (M := M) (∞ : WithTop ℕ∞) T theta y)
        K =
      contractUpper
        (fun L : Fin r -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I) (fun x => X x) x₀
            (fun x => theta x) L)
        (fun L : Fin r -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          fun K : Fin s -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
            DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt (I := I) (T x₀) L K)
        K +
      contractUpper
        (fun L : Fin r -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt (I := I) (theta x₀) L)
        (fun L : Fin r -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          fun K : Fin s -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
            DifferentialGeometry.Tensor.Coordinates.coordDerivRSAt (I := I) (fun x => X x) x₀
              (fun x => T x) L K)
        K  := by sorry

theorem mixedRicciIdentityCoord_of_coordinate_second_product
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta beta_i beta_j beta_ij beta_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commContract contract_ij contract_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commProbe probe_i probe_j probe_ij probe_ji :
      (Fin r -> Idx) -> (Fin r -> Idx) -> Real)
    (prod_ij_left prod_ij_right prod_ji_left prod_ji_right :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (hcommBeta : ∀ L K, commBeta L K = beta_ij L K - beta_ji L K)
    (hcommContract : ∀ L K, commContract L K = contract_ij L K - contract_ji L K)
    (hcommProbe : ∀ L A, commProbe L A = probe_ij L A - probe_ji L A)
    (hcontract_ij : ∀ L K,
      contract_ij L K = prod_ij_left L K + prod_ij_right L K)
    (hprod_ij_left : ∀ L K,
      prod_ij_left L K =
        contractUpper (probe_ij L) beta K +
          contractUpper (probe_j L) beta_i K)
    (hprod_ij_right : ∀ L K,
      prod_ij_right L K =
        contractUpper (probe_i L) beta_j K +
          contractUpper (deltaMulti L) beta_ij K)
    (hcontract_ji : ∀ L K,
      contract_ji L K = prod_ji_left L K + prod_ji_right L K)
    (hprod_ji_left : ∀ L K,
      prod_ji_left L K =
        contractUpper (probe_ji L) beta K +
          contractUpper (probe_i L) beta_j K)
    (hprod_ji_right : ∀ L K,
      prod_ji_right L K =
        contractUpper (probe_j L) beta_i K +
          contractUpper (deltaMulti L) beta_ji K)
    (hcontractCov : ∀ L K,
      commContract L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K)
    (hprobeCov : ∀ L A,
      commProbe L A = covariantCurvAction R i j (deltaMulti L) A) :
    MixedRicciIdentityCoord R i j commBeta beta  := by sorry

end MixedComponentAlgebra

end DifferentialGeometry.Tensor.RicciIdentity

