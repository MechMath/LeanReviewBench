import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import dep.DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra



set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SyntheticTensor






abbrev TensorData (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    (r s : ℕ) :=
  MultilinearMap R (fun _ : Fin s => V)
    (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)


abbrev AbstractTensor (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    (r s : ℕ) := TensorData R V r s





section Helpers
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def evalLinear (v : V) : (V →ₗ[R] R) →ₗ[R] R where
  toFun α := α v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


def scalarToData (f : R) : TensorData R V 0 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => (V →ₗ[R] R)) f)


def vectorToData (v : V) : TensorData R V 1 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.ofSubsingleton R (V →ₗ[R] R) R (0 : Fin 1) (evalLinear v))


def covectorToData (α : V →ₗ[R] R) : TensorData R V 0 1 where
  toFun m := MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => (V →ₗ[R] R)) (α (m 0))
  map_update_add' m i x y := by
    have hi : i = 0 := Subsingleton.elim _ _; subst hi
    simp only [Function.update_self]
    ext n; simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.add_apply]
    exact map_add α x y
  map_update_smul' m i c x := by
    have hi : i = 0 := Subsingleton.elim _ _; subst hi
    simp only [Function.update_self]
    ext n; simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.smul_apply, smul_eq_mul]
    exact α.map_smul c x

@[simp] theorem covectorToData_eval (α : V →ₗ[R] R) (v : V) :
    covectorToData (R := R) α ![v] ![] = α v  := by sorry

end Helpers





section EvalExt
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def tensor_eval {r s : ℕ} (T : TensorData R V r s)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) : R :=
  T vs αs


theorem tensor_ext {r s : ℕ} (T₁ T₂ : TensorData R V r s)
    (h : ∀ vs αs, tensor_eval T₁ vs αs = tensor_eval T₂ vs αs) : T₁ = T₂  := by sorry

end EvalExt





section Swap
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def swap_covariant {r s : ℕ} (i j : Fin s) (T : TensorData R V r s) :
    TensorData R V r s :=
  T.domDomCongr (Equiv.swap i j)


def swap_contravariant {r s : ℕ} (i j : Fin r) (T : TensorData R V r s) :
    TensorData R V r s where
  toFun m := (T m).domDomCongr (Equiv.swap i j)
  map_update_add' := by
    intro _ m k x y; ext n
    change (T (Function.update m k (x + y))) (n ∘ Equiv.swap i j) =
         (T (Function.update m k x)) (n ∘ Equiv.swap i j) +
         (T (Function.update m k y)) (n ∘ Equiv.swap i j)
    rw [T.map_update_add]; rfl
  map_update_smul' := by
    intro _ m k c x; ext n
    change (T (Function.update m k (c • x))) (n ∘ Equiv.swap i j) =
         c • (T (Function.update m k x)) (n ∘ Equiv.swap i j)
    rw [T.map_update_smul]; rfl

theorem swap_covariant_eval {r s : ℕ} (i j : Fin s) (T : TensorData R V r s)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    swap_covariant i j T m n = T (m ∘ Equiv.swap i j) n  := by sorry

theorem swap_contravariant_eval {r s : ℕ} (i j : Fin r) (T : TensorData R V r s)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    swap_contravariant i j T m n = T m (n ∘ Equiv.swap i j)  := by sorry

end Swap





section TensorProd
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


noncomputable def tensor_prod {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : TensorData R V r₁ s₁) (T₂ : TensorData R V r₂ s₂) :
    TensorData R V (r₁ + r₂) (s₁ + s₂) where
  toFun m :=
    { toFun := fun n =>
        T₁ (m ∘ Fin.castAdd s₂) (n ∘ Fin.castAdd r₂) *
        T₂ (m ∘ Fin.natAdd s₁) (n ∘ Fin.natAdd r₁)
      map_update_add' := by
        intro _ n i x y
        by_cases h : i.val < r₁
        · let j : Fin r₁ := ⟨i.val, h⟩
          have hj : Fin.castAdd r₂ j = i := Fin.ext rfl
          have hc : ∀ v, Function.update n i v ∘ Fin.castAdd r₂ =
              Function.update (n ∘ Fin.castAdd r₂) j v := fun v => by
            rw [← hj]; exact Function.update_comp_eq_of_injective n
              (Fin.castAdd_injective r₁ r₂) j v
          have hn : ∀ v, Function.update n i v ∘ Fin.natAdd r₁ = n ∘ Fin.natAdd r₁ := fun v =>
            Function.update_comp_eq_of_forall_ne n v
              (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
          simp only [hc, hn, (T₁ (m ∘ Fin.castAdd s₂)).map_update_add]
          ring
        · push Not at h
          let j : Fin r₂ := ⟨i.val - r₁, by omega⟩
          have hj : Fin.natAdd r₁ j = i := Fin.ext (by change r₁ + (i.val - r₁) = i.val; omega)
          have hc : ∀ v, Function.update n i v ∘ Fin.natAdd r₁ =
              Function.update (n ∘ Fin.natAdd r₁) j v := fun v => by
            rw [← hj]; exact Function.update_comp_eq_of_injective n
              (Fin.natAdd_injective r₂ r₁) j v
          have hn : ∀ v, Function.update n i v ∘ Fin.castAdd r₂ = n ∘ Fin.castAdd r₂ := fun v =>
            Function.update_comp_eq_of_forall_ne n v
              (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
          simp only [hc, hn, (T₂ (m ∘ Fin.natAdd s₁)).map_update_add]
          ring
      map_update_smul' := by
        intro _ n i c x
        by_cases h : i.val < r₁
        · let j : Fin r₁ := ⟨i.val, h⟩
          have hj : Fin.castAdd r₂ j = i := Fin.ext rfl
          have hc : ∀ v, Function.update n i v ∘ Fin.castAdd r₂ =
              Function.update (n ∘ Fin.castAdd r₂) j v := fun v => by
            rw [← hj]; exact Function.update_comp_eq_of_injective n
              (Fin.castAdd_injective r₁ r₂) j v
          have hn : ∀ v, Function.update n i v ∘ Fin.natAdd r₁ = n ∘ Fin.natAdd r₁ := fun v =>
            Function.update_comp_eq_of_forall_ne n v
              (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
          simp only [hc, hn, (T₁ (m ∘ Fin.castAdd s₂)).map_update_smul, smul_eq_mul]
          ring
        · push Not at h
          let j : Fin r₂ := ⟨i.val - r₁, by omega⟩
          have hj : Fin.natAdd r₁ j = i := Fin.ext (by change r₁ + (i.val - r₁) = i.val; omega)
          have hc : ∀ v, Function.update n i v ∘ Fin.natAdd r₁ =
              Function.update (n ∘ Fin.natAdd r₁) j v := fun v => by
            rw [← hj]; exact Function.update_comp_eq_of_injective n
              (Fin.natAdd_injective r₂ r₁) j v
          have hn : ∀ v, Function.update n i v ∘ Fin.castAdd r₂ = n ∘ Fin.castAdd r₂ := fun v =>
            Function.update_comp_eq_of_forall_ne n v
              (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
          simp only [hc, hn, (T₂ (m ∘ Fin.natAdd s₁)).map_update_smul, smul_eq_mul]
          ring }
  map_update_add' := by
    intro _ m i x y; ext n
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    by_cases h : i.val < s₁
    · let j : Fin s₁ := ⟨i.val, h⟩
      have hj : Fin.castAdd s₂ j = i := Fin.ext rfl
      have hc : ∀ v, Function.update m i v ∘ Fin.castAdd s₂ =
          Function.update (m ∘ Fin.castAdd s₂) j v := fun v => by
        rw [← hj]; exact Function.update_comp_eq_of_injective m
          (Fin.castAdd_injective s₁ s₂) j v
      have hn : ∀ v, Function.update m i v ∘ Fin.natAdd s₁ = m ∘ Fin.natAdd s₁ := fun v =>
        Function.update_comp_eq_of_forall_ne m v
          (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
      simp only [hc, hn, T₁.map_update_add, MultilinearMap.add_apply]
      ring
    · push Not at h
      let j : Fin s₂ := ⟨i.val - s₁, by omega⟩
      have hj : Fin.natAdd s₁ j = i := Fin.ext (by change s₁ + (i.val - s₁) = i.val; omega)
      have hc : ∀ v, Function.update m i v ∘ Fin.natAdd s₁ =
          Function.update (m ∘ Fin.natAdd s₁) j v := fun v => by
        rw [← hj]; exact Function.update_comp_eq_of_injective m
          (Fin.natAdd_injective s₂ s₁) j v
      have hn : ∀ v, Function.update m i v ∘ Fin.castAdd s₂ = m ∘ Fin.castAdd s₂ := fun v =>
        Function.update_comp_eq_of_forall_ne m v
          (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
      simp only [hc, hn, T₂.map_update_add, MultilinearMap.add_apply]
      ring
  map_update_smul' := by
    intro _ m i c x; ext n
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    by_cases h : i.val < s₁
    · let j : Fin s₁ := ⟨i.val, h⟩
      have hj : Fin.castAdd s₂ j = i := Fin.ext rfl
      have hc : ∀ v, Function.update m i v ∘ Fin.castAdd s₂ =
          Function.update (m ∘ Fin.castAdd s₂) j v := fun v => by
        rw [← hj]; exact Function.update_comp_eq_of_injective m
          (Fin.castAdd_injective s₁ s₂) j v
      have hn : ∀ v, Function.update m i v ∘ Fin.natAdd s₁ = m ∘ Fin.natAdd s₁ := fun v =>
        Function.update_comp_eq_of_forall_ne m v
          (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
      simp only [hc, hn, T₁.map_update_smul, MultilinearMap.smul_apply, smul_eq_mul]
      ring
    · push Not at h
      let j : Fin s₂ := ⟨i.val - s₁, by omega⟩
      have hj : Fin.natAdd s₁ j = i := Fin.ext (by change s₁ + (i.val - s₁) = i.val; omega)
      have hc : ∀ v, Function.update m i v ∘ Fin.natAdd s₁ =
          Function.update (m ∘ Fin.natAdd s₁) j v := fun v => by
        rw [← hj]; exact Function.update_comp_eq_of_injective m
          (Fin.natAdd_injective s₂ s₁) j v
      have hn : ∀ v, Function.update m i v ∘ Fin.castAdd s₂ = m ∘ Fin.castAdd s₂ := fun v =>
        Function.update_comp_eq_of_forall_ne m v
          (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
      simp only [hc, hn, T₂.map_update_smul, MultilinearMap.smul_apply, smul_eq_mul]
      ring

theorem tensor_prod_eval {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : TensorData R V r₁ s₁) (T₂ : TensorData R V r₂ s₂)
    (m : Fin (s₁ + s₂) → V) (n : Fin (r₁ + r₂) → (V →ₗ[R] R)) :
    tensor_prod T₁ T₂ m n =
    T₁ (m ∘ Fin.castAdd s₂) (n ∘ Fin.castAdd r₂) *
    T₂ (m ∘ Fin.natAdd s₁) (n ∘ Fin.natAdd r₁)  := by sorry

end TensorProd





section CovectorFromTensor
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def covector_from_tensor {r s : ℕ} (D : TensorData R V r (s + 1))
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) : V →ₗ[R] R where
  toFun w := D (Fin.cons w m) n
  map_add' x y := by
    change D.curryLeft (x + y) m n = D.curryLeft x m n + D.curryLeft y m n
    rw [D.curryLeft.map_add, MultilinearMap.add_apply, MultilinearMap.add_apply]
  map_smul' c x := by
    change D.curryLeft (c • x) m n = c • (D.curryLeft x m n)
    rw [D.curryLeft.map_smul, MultilinearMap.smul_apply, MultilinearMap.smul_apply]

end CovectorFromTensor





section EndoToTensorDef
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def endo_to_tensor (L : V →ₗ[R] V) : TensorData R V 1 1 where
  toFun m :=
    { toFun := fun n => n 0 (L (m 0))
      map_update_add' := by
        intro _ n i x y
        have hi := Subsingleton.elim i 0; subst hi
        simp [Function.update_self]
      map_update_smul' := by
        intro _ n i c x
        have hi := Subsingleton.elim i 0; subst hi
        simp [Function.update_self, smul_eq_mul] }
  map_update_add' := by
    intro _ m i x y; ext n
    have hi := Subsingleton.elim i 0; subst hi
    simp only [Function.update_self, MultilinearMap.coe_mk, MultilinearMap.add_apply, map_add]
  map_update_smul' := by
    intro _ m i c x; ext n
    have hi := Subsingleton.elim i 0; subst hi
    simp only [Function.update_self, MultilinearMap.coe_mk, MultilinearMap.smul_apply,
      smul_eq_mul, map_smul]

theorem endo_to_tensor_eval (L : V →ₗ[R] V) (v : V) (α : V →ₗ[R] R) :
    endo_to_tensor L ![v] ![α] = α (L v)  := by sorry

end EndoToTensorDef






structure AbstractTrace (R V : Type*)
    [CommRing R] [AddCommGroup V] [Module R V] where
  
  tr : (V →ₗ[R] V) →ₗ[R] R
  
  trace_outer : ∀ (v : V) (α : V →ₗ[R] R), tr (α.smulRight v) = α v
  
  trace_comm : ∀ (A B : V →ₗ[R] V), tr (A * B) = tr (B * A)
  
  tensor_contract {r s : ℕ} :
    TensorData R V (r + 1) (s + 1) → TensorData R V r s
  
  tensor_contract_add {r s : ℕ} (T₁ T₂ : TensorData R V (r + 1) (s + 1)) :
    tensor_contract (T₁ + T₂) = tensor_contract T₁ + tensor_contract T₂
  
  tensor_contract_smul {r s : ℕ} (c : R) (T : TensorData R V (r + 1) (s + 1)) :
    tensor_contract (c • T) = c • tensor_contract T
  
  data_eval_single_contract {r s : ℕ}
    (D : TensorData R V r (s + 1)) (v : V)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    (tensor_contract
      ((show 1 + r = r + 1 from by omega) ▸
       (show 0 + (s + 1) = s + 1 from by omega) ▸
       tensor_prod (r₁ := 1) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
         (vectorToData (R := R) v) D)) m n =
    D (Fin.cons v m) n
  
  data_eval_single_contract_dual {r s₁ s₂ : ℕ}
    (A : TensorData R V 0 (s₁ + 1)) (B : TensorData R V (r + 1) s₂)
    (m : Fin (s₁ + s₂) → V) (n : Fin r → (V →ₗ[R] R)) :
    (tensor_contract
      ((show 0 + (r + 1) = r + 1 from by omega) ▸
       (show (s₁ + 1) + s₂ = (s₁ + s₂) + 1 from by omega) ▸
       tensor_prod (r₁ := 0) (s₁ := s₁ + 1) (r₂ := r + 1) (s₂ := s₂) A B)) m n =
    B (m ∘ Fin.natAdd s₁) (Fin.cons (covector_from_tensor A (m ∘ Fin.castAdd s₂) ![]) n)
  
  tensor_contract_endo (L : V →ₗ[R] V) :
    (tensor_contract (endo_to_tensor L)) ![] ![] = tr L





section ScalarVector
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def toScalar (T : TensorData R V 0 0) : R := T ![] ![]
def fromScalar (f : R) : TensorData R V 0 0 := scalarToData f
def fromVector (v : V) : TensorData R V 1 0 := vectorToData v

theorem toScalar_fromScalar (f : R) : toScalar (fromScalar f : TensorData R V 0 0) = f  := by sorry

theorem fromVector_eval (v : V) (α : V →ₗ[R] R) :
    vectorToData (R := R) v ![] ![α] = α v  := by sorry

end ScalarVector





section EndoTensor
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def delta_tensor : TensorData R V 1 1 := endo_to_tensor LinearMap.id

theorem delta_tensor_eval (v : V) (α : V →ₗ[R] R) :
    (delta_tensor : TensorData R V 1 1) ![v] ![α] = α v  := by sorry

def outerProduct (v : V) (α : V →ₗ[R] R) : V →ₗ[R] V := α.smulRight v

end EndoTensor





section Contract
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def contract (atr : AbstractTrace R V) (L : V →ₗ[R] V) : R := atr.tr L


theorem contract_outerProduct (atr : AbstractTrace R V) (v : V) (α : V →ₗ[R] R) :
    contract atr (outerProduct v α) = α v  := by sorry

theorem contract_comm (atr : AbstractTrace R V) (A B : V →ₗ[R] V) :
    contract atr (A * B) = contract atr (B * A)  := by sorry

theorem contract_add (atr : AbstractTrace R V) (L₁ L₂ : V →ₗ[R] V) :
    contract atr (L₁ + L₂) = contract atr L₁ + contract atr L₂  := by sorry

theorem contract_smul (atr : AbstractTrace R V) (c : R) (L : V →ₗ[R] V) :
    contract atr (c • L) = c * contract atr L  := by sorry

end Contract





section EvalContract
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def eval_endo {r s : ℕ} (D : TensorData R V r (s + 1)) (v : V)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) : V →ₗ[R] V :=
  outerProduct v (covector_from_tensor D m n)


theorem data_eval_single_contract (atr : AbstractTrace R V) {r s : ℕ}
    (D : TensorData R V r (s + 1)) (v : V)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    contract atr (eval_endo D v m n) = D (Fin.cons v m) n  := by sorry

end EvalContract





section Bilinearity
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem tensor_eval_add {r s : ℕ} (T₁ T₂ : TensorData R V r s)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) :
    tensor_eval (T₁ + T₂) vs αs = tensor_eval T₁ vs αs + tensor_eval T₂ vs αs  := by sorry

theorem tensor_eval_smul {r s : ℕ} (c : R) (T : TensorData R V r s)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) :
    tensor_eval (c • T) vs αs = c * tensor_eval T vs αs  := by sorry

theorem vectorToData_add (X Y : V) :
    vectorToData (R := R) (X + Y) = vectorToData X + vectorToData Y  := by sorry

theorem vectorToData_smul (c : R) (X : V) :
    vectorToData (R := R) (c • X) = c • vectorToData X  := by sorry

end Bilinearity





section GeneralContract
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]


def contract_general (atr : AbstractTrace R V) {r s : ℕ}
    (i : Fin (r + 1)) (j : Fin (s + 1))
    (T : TensorData R V (r + 1) (s + 1)) : TensorData R V r s :=
  atr.tensor_contract (swap_covariant 0 j (swap_contravariant 0 i T))

theorem contract_general_add (atr : AbstractTrace R V) {r s : ℕ}
    (i : Fin (r + 1)) (j : Fin (s + 1))
    (T₁ T₂ : TensorData R V (r + 1) (s + 1)) :
    contract_general atr i j (T₁ + T₂) =
    contract_general atr i j T₁ + contract_general atr i j T₂  := by sorry

theorem contract_general_smul (atr : AbstractTrace R V) {r s : ℕ}
    (i : Fin (r + 1)) (j : Fin (s + 1))
    (c : R) (T : TensorData R V (r + 1) (s + 1)) :
    contract_general atr i j (c • T) =
    c • contract_general atr i j T  := by sorry

theorem contract_general_0_0 (atr : AbstractTrace R V) {r s : ℕ}
    (T : TensorData R V (r + 1) (s + 1)) :
    contract_general atr 0 0 T = atr.tensor_contract T  := by sorry

end GeneralContract






def NablaTrComm {k R V : Type*}
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (conn_nabla : V → V → V)
    (conn_add : ∀ X Y Z, conn_nabla X (Y + Z) = conn_nabla X Y + conn_nabla X Z)
    (conn_leibniz : ∀ X (f : R) Y, conn_nabla X (f • Y) =
      (emb.embed X) f • Y + f • conn_nabla X Y) : Prop :=
  ∀ (X : V) (L : V →ₗ[R] V),
    (emb.embed X) (atr.tr L) = atr.tr (commutatorEndo
      (emb.embed X).toFun (conn_nabla X)
      (conn_add X) (conn_leibniz X) L)


def TimeTrComm {R V : Type*} {A Time : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    [CommRing A] [Algebra R A]
    (atr : AbstractTrace R V) (td : TimeDerivativeData R A Time) : Prop :=
  ∀ (L : Time → V →ₗ[R] V) (dL : V →ₗ[R] V) (t : Time)
    (αLv : V → (V →ₗ[R] R) → A) (trL : A),
    (∀ v α s, td.eval (αLv v α) s = α (L s v)) →
    (∀ s, td.eval trL s = atr.tr (L s)) →
    (∀ (v : V) (α : V →ₗ[R] R), α (dL v) = td.eval (td.dt (αLv v α)) t) →
    td.eval (td.dt trL) t = atr.tr dL


theorem TimeTrComm.of_pi {R V Time : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    {atr : AbstractTrace R V} {td : TimeDerivativeData R (Time → R) Time}
    [TimeRegularFam td]
    (h : TimeTrComm atr td)
    (L : Time → V →ₗ[R] V) (dL : V →ₗ[R] V) (t : Time)
    (h_αLv_smooth : ∀ (v : V) (α : V →ₗ[R] R),
      td.isSmoothFam (fun s => α (L s v)))
    (h_trL_smooth : td.isSmoothFam (fun s => atr.tr (L s)))
    (h_char : ∀ (v : V) (α : V →ₗ[R] R),
      α (dL v) = td.eval (td.dt (td.lift (fun s => α (L s v)))) t) :
    td.eval (td.dt (td.lift (fun s => atr.tr (L s)))) t = atr.tr dL  := by sorry

end SyntheticTensor
