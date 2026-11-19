import dep.DifferentialGeometry.Tensor.RSTensor.Defs

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section Lowering

variable {x : M}

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_one_apply_add
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    α (fun _ : Fin 1 => X + Y) =
      α (fun _ : Fin 1 => X) + α (fun _ : Fin 1 => Y)  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_one_apply_smul
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (c : Real) (X : TangentSpace I x) :
    α (fun _ : Fin 1 => c • X) =
      c • α (fun _ : Fin 1 => X)  := by sorry

private noncomputable def bilinearCovectorCompSlot
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X : TangentSpace I x) :
    TangentSpace I x →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => α (fun _ : Fin 1 => (A Y) X)
      map_add' := by
        intro Y Z
        change α (fun _ : Fin 1 => (A (Y + Z)) X) =
          α (fun _ : Fin 1 => (A Y) X) + α (fun _ : Fin 1 => (A Z) X)
        rw [map_add]
        exact tensor0S_one_apply_add (I := I) α ((A Y) X) ((A Z) X)
      map_smul' := by
        intro c Y
        change α (fun _ : Fin 1 => (A (c • Y)) X) =
          c • α (fun _ : Fin 1 => (A Y) X)
        rw [map_smul]
        exact tensor0S_one_apply_smul (I := I) α c ((A Y) X) }

noncomputable def bilinearCovectorComp
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
    (ContinuousLinearMap.uncurryLeft
      (𝕜 := Real) (n := 1) (Ei := fun _ : Fin 2 => TangentSpace I x) (G := Real)
      (LinearMap.toContinuousLinearMap
        { toFun := fun X =>
            (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
              (bilinearCovectorCompSlot (I := I) A α X)
          map_add' := by
            intro X Y
            apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
            ext Z
            change α (fun _ : Fin 1 => (A Z) (X + Y)) =
              α (fun _ : Fin 1 => (A Z) X) + α (fun _ : Fin 1 => (A Z) Y)
            rw [map_add]
            exact tensor0S_one_apply_add (I := I) α ((A Z) X) ((A Z) Y)
          map_smul' := by
            intro c X
            apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
            ext Z
            change α (fun _ : Fin 1 => (A Z) (c • X)) =
              c • α (fun _ : Fin 1 => (A Z) X)
            rw [map_smul]
            exact tensor0S_one_apply_smul (I := I) α c ((A Z) X) }))

@[simp]
theorem bilinearCovectorComp_apply
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (v : Fin 2 -> TangentSpace I x) :
    Tensor0SSpace.eval (bilinearCovectorComp (I := I) A α) v =
      Tensor0SSpace.eval α (fun _ : Fin 1 => (A (v 1)) (v 0))  := by sorry

theorem bilinearCovectorComp_apply_slots
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    Tensor0SSpace.eval (bilinearCovectorComp (I := I) A α)
        (fun q : Fin 2 => if q = 0 then X else Y) =
      Tensor0SSpace.eval α (fun _ : Fin 1 => (A Y) X)  := by sorry

def bilinearToTensor
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => bilinearCovectorComp (I := I) A α
      map_add' := by
        intro α β
        apply ContinuousMultilinearMap.ext
        intro v
        change Tensor0SSpace.eval (bilinearCovectorComp (I := I) A (α + β)) v =
          Tensor0SSpace.eval
            (bilinearCovectorComp (I := I) A α + bilinearCovectorComp (I := I) A β) v
        rw [bilinearCovectorComp_apply]
        change Tensor0SSpace.eval (α + β) (fun _ : Fin 1 => (A (v 1)) (v 0)) = _
        rw [Tensor0SSpace.eval_add]
        rw [Tensor0SSpace.eval_add, bilinearCovectorComp_apply,
          bilinearCovectorComp_apply]
      map_smul' := by
        intro c α
        apply ContinuousMultilinearMap.ext
        intro v
        change Tensor0SSpace.eval (bilinearCovectorComp (I := I) A (c • α)) v =
          Tensor0SSpace.eval (c • bilinearCovectorComp (I := I) A α) v
        rw [bilinearCovectorComp_apply]
        change Tensor0SSpace.eval (c • α) (fun _ : Fin 1 => (A (v 1)) (v 0)) = _
        rw [Tensor0SSpace.eval_smul]
        rw [Tensor0SSpace.eval_smul, bilinearCovectorComp_apply] }

@[simp]
theorem bilinearToTensor_apply
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (v : Fin 2 -> TangentSpace I x) :
    Tensor0SSpace.eval (bilinearToTensor (I := I) A α) v =
      Tensor0SSpace.eval α (fun _ : Fin 1 => (A (v 1)) (v 0))  := by sorry

private def lowerBilinOut (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x).symm
    (ContinuousLinearMap.uncurryLeft (𝕜 := Real) (n := 2)
      (Ei := fun _ : Fin 3 => TangentSpace I x) (G := Real)
      (LinearMap.toContinuousLinearMap
        { toFun := fun W =>
            tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
              (bilinearToTensor (I := I) A
                ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 1 x).symm
                  (ContinuousMultilinearMap.curryLeft
                    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x q) W)))
          map_add' := by
            intro W₁ W₂
            rw [map_add, map_add, map_add, map_add]
          map_smul' := by
            intro c W
            rw [map_smul, map_smul, map_smul, map_smul, RingHom.id_apply] }))

private theorem lowerBilinOut_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (w : Fin 3 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerBilinOut (I := I) q A) w =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then w 0 else (A (w 2)) (w 1))  := by sorry

private def lowerStdPerm : Equiv.Perm (Fin 3) where
  toFun i := if i = 0 then 2 else if i = 1 then 0 else 1
  invFun i := if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv i := by fin_cases i <;> simp
  right_inv i := by fin_cases i <;> simp

def lowerBilin (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  Tensor0SSpace.domDomCongr
    (lowerBilinOut (I := I)
      (Tensor0SSpace.domDomCongr q (Equiv.swap (0 : Fin 2) 1)) A)
    lowerStdPerm

theorem lowerBilin_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (v : Fin 3 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerBilin (I := I) q A) v =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then (A (v 1)) (v 0) else v 2)  := by sorry

end Lowering

section Expansion

variable {x : M}

omit [FiniteDimensional ℝ E] in
theorem tensor02_expand {ι : Type*} [Fintype ι]
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (b : Module.Basis ι Real (TangentSpace I x)) (W Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then W else Z) =
      ∑ k, b.repr W k * q (fun a : Fin 2 => if a = 0 then b k else Z)  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem bilin_expand {ι : Type*} [Fintype ι]
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (b : Module.Basis ι Real (TangentSpace I x)) (X Y : TangentSpace I x) :
    (A Y) X = ∑ j, ∑ i, (b.repr Y j * b.repr X i) • (A (b j)) (b i)  := by sorry

end Expansion

end DifferentialGeometry.Tensor0SBundle

end

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section Lowering

variable {x : M}

omit [FiniteDimensional ℝ E] in
private theorem tensor02_add_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z) =
      Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
        Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₂ else Z)  := by sorry

omit [FiniteDimensional ℝ E] in
private theorem tensor02_smul_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real) (u Z : TangentSpace I x) :
    Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then c • u else Z) =
      c * Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u else Z)  := by sorry

private theorem lowerBilin_add
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A B : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    lowerBilin (I := I) q (A + B) =
      lowerBilin (I := I) q A + lowerBilin (I := I) q B  := by sorry

private theorem lowerBilin_smul
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    lowerBilin (I := I) q (c • A) = c • lowerBilin (I := I) q A  := by sorry

private def lowerTriOut
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ContinuousLinearMap.uncurryLeft (𝕜 := Real) (n := 3)
    (Ei := fun _ : Fin 4 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X =>
          (lowerBilin (I := I) q (A X) :
            ContinuousMultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real)
        map_add' := by
          intro X₁ X₂
          rw [map_add]
          exact lowerBilin_add (I := I) q (A X₁) (A X₂)
        map_smul' := by
          intro c X
          rw [map_smul]
          exact lowerBilin_smul (I := I) q c (A X) })

private theorem lowerTriOut_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (w : Fin 4 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerTriOut (I := I) q A) w =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then ((A (w 0)) (w 2)) (w 1) else w 3)  := by sorry

def lowerTri
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 4) 2)
    (lowerTriOut (I := I) q A)

theorem lowerTri_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (v : Fin 4 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerTri (I := I) q A) v =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then ((A (v 0)) (v 1)) (v 2) else v 3)  := by sorry

end Lowering

end DifferentialGeometry.Tensor0SBundle

end

