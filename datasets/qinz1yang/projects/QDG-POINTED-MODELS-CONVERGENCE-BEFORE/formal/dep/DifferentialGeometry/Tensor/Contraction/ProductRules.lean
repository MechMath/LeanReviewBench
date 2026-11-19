import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

open scoped BigOperators

namespace DifferentialGeometry.Tensor.Contraction

def contractUpper {R Idx : Type*} [AddCommMonoid R] [Mul R] [Fintype Idx]
    {r s : Nat}
    (theta : (Fin r -> Idx) -> R)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> R)
    (K : Fin s -> Idx) : R :=
  ∑ L : Fin r -> Idx, theta L * beta L K

theorem contractUpper_commutator_of_second_product_rules
    {R Idx : Type*} [NonUnitalNonAssocRing R] [Fintype Idx] {r s : Nat}
    (theta theta_i theta_j theta_ij theta_ji : (Fin r -> Idx) -> R)
    (beta beta_i beta_j beta_ij beta_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> R)
    (contract_ij contract_ji : (Fin s -> Idx) -> R)
    (hij : ∀ K,
      contract_ij K =
        contractUpper theta_ij beta K +
          contractUpper theta_j beta_i K +
          contractUpper theta_i beta_j K +
          contractUpper theta beta_ij K)
    (hji : ∀ K,
      contract_ji K =
        contractUpper theta_ji beta K +
          contractUpper theta_i beta_j K +
          contractUpper theta_j beta_i K +
          contractUpper theta beta_ji K)
    (K : Fin s -> Idx) :
    contractUpper theta (fun L K => beta_ij L K - beta_ji L K) K =
      (contract_ij K - contract_ji K) -
        contractUpper (fun L => theta_ij L - theta_ji L) beta K  := by sorry

theorem contractUpper_second_product_of_first_product_rules
    {R Idx : Type*} [AddCommMonoid R] [Mul R] [Fintype Idx] {r s : Nat}
    (theta theta_i theta_j theta_ij : (Fin r -> Idx) -> R)
    (beta beta_i beta_j beta_ij :
      (Fin r -> Idx) -> (Fin s -> Idx) -> R)
    (contract_ij left right : (Fin s -> Idx) -> R)
    (hcontract : ∀ K, contract_ij K = left K + right K)
    (hleft : ∀ K,
      left K =
        contractUpper theta_ij beta K +
          contractUpper theta_j beta_i K)
    (hright : ∀ K,
      right K =
        contractUpper theta_i beta_j K +
          contractUpper theta beta_ij K)
    (K : Fin s -> Idx) :
    contract_ij K =
      contractUpper theta_ij beta K +
        contractUpper theta_j beta_i K +
        contractUpper theta_i beta_j K +
        contractUpper theta beta_ij K  := by sorry

theorem contractUpper_first_product_of_local_rules
    {R Ω Idx : Type*} [AddCommMonoid R] [Mul R] [Fintype Idx] {r s : Nat}
    (D : (Ω -> R) -> R) (z₀ : Ω)
    (theta : Ω -> (Fin r -> Idx) -> R)
    (beta : Ω -> (Fin r -> Idx) -> (Fin s -> Idx) -> R)
    (thetaD : (Fin r -> Idx) -> R)
    (betaD : (Fin r -> Idx) -> (Fin s -> Idx) -> R)
    (K : Fin s -> Idx)
    (hDsum :
      D (fun z => ∑ A : Fin r -> Idx, theta z A * beta z A K) =
        ∑ A : Fin r -> Idx, D (fun z => theta z A * beta z A K))
    (hDmul : ∀ A : Fin r -> Idx,
      D (fun z => theta z A * beta z A K) =
        thetaD A * beta z₀ A K + theta z₀ A * betaD A K) :
    D (fun z => contractUpper (theta z) (beta z) K) =
      contractUpper thetaD (fun A K => beta z₀ A K) K +
        contractUpper (theta z₀) betaD K  := by sorry

theorem contractUpper_first_product_of_scalar_derivation
    {R Ω Idx : Type*} [AddCommMonoid R] [Mul R] [Fintype Idx] {r s : Nat}
    (D : (Ω -> R) -> R) (z₀ : Ω)
    (theta : Ω -> (Fin r -> Idx) -> R)
    (beta : Ω -> (Fin r -> Idx) -> (Fin s -> Idx) -> R)
    (thetaD : (Fin r -> Idx) -> R)
    (betaD : (Fin r -> Idx) -> (Fin s -> Idx) -> R)
    (hDsum : ∀ f : (Fin r -> Idx) -> Ω -> R,
      D (fun z => ∑ A : Fin r -> Idx, f A z) =
        ∑ A : Fin r -> Idx, D (f A))
    (hDmul : ∀ f g : Ω -> R,
      D (fun z => f z * g z) = D f * g z₀ + f z₀ * D g)
    (hthetaD : ∀ A, D (fun z => theta z A) = thetaD A)
    (hbetaD : ∀ A K, D (fun z => beta z A K) = betaD A K)
    (K : Fin s -> Idx) :
    D (fun z => contractUpper (theta z) (beta z) K) =
      contractUpper thetaD (fun A K => beta z₀ A K) K +
        contractUpper (theta z₀) betaD K  := by sorry

end DifferentialGeometry.Tensor.Contraction

