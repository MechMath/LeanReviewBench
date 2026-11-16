# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

## Recorded migration rationale

# SP-A-CUTOFF-FIXED：修复版 Formal 与兼容说明

原负例：`SP-A-CUTOFF`；修复快照：`cce794efc489e57fa9bcb3dc831bcd92d4a05c14`。
root：`MagicFunction.a.SpecialValues.a_zero`；源路径：`SpherePacking/MagicFunction/a/SpecialValues.lean:25`。
上游 PR #485；修复提交 `cce794efc489e57fa9bcb3dc831bcd92d4a05c14`。

## 固定 Formal

```lean
@Eq Complex
  (@DFunLike.coe
    (↥(@RadialSchwartzMap Complex (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
        Complex Complex.instNormedField
        (@PiLp.normedAddCommGroup
          (@OfNat.ofNat ENNReal (nat_lit 2)
            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
              (@AddMonoidWithOne.toNatCast ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
              PiLp.innerProductSpace._proof_1))
          (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fact_one_le_two_ennreal
          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) fun i => Real.normedAddCommGroup)
        (@PiLp.normedSpace
          (@OfNat.ofNat ENNReal (nat_lit 2)
            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
              (@AddMonoidWithOne.toNatCast ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
              PiLp.innerProductSpace._proof_1))
          Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fact_one_le_two_ennreal
          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) Real.normedField
          (fun i =>
            @NonUnitalSeminormedRing.toSeminormedAddCommGroup Real
              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Real
                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Real
                  (@NormedCommRing.toSeminormedCommRing Real Real.normedCommRing))))
          fun i =>
          @InnerProductSpace.toNormedSpace Real Real Real.instRCLike
            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Real
              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Real
                (@SeminormedCommRing.toNonUnitalSeminormedCommRing Real
                  (@NormedCommRing.toSeminormedCommRing Real Real.normedCommRing))))
            (@RCLike.toInnerProductSpaceReal Real Real.instRCLike))
        Complex.instNormedAddCommGroup
        (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
          instInnerProductSpaceRealComplex)
        (@NonUnitalCStarAlgebra.toNormedSpace Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))
        ⋯))
    (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) (fun x => Complex)
    (@RadialSchwartzMap.instFunLike Complex
      (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) Complex
      Complex.instNormedField
      (@PiLp.normedAddCommGroup
        (@OfNat.ofNat ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
            PiLp.innerProductSpace._proof_1))
        (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fact_one_le_two_ennreal
        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) fun i => Real.normedAddCommGroup)
      Complex.instNormedAddCommGroup
      (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
        instInnerProductSpaceRealComplex)
      (@NonUnitalCStarAlgebra.toNormedSpace Complex
        (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
          (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))
      ⋯
      (@PiLp.normedSpace
        (@OfNat.ofNat ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
            PiLp.innerProductSpace._proof_1))
        Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fact_one_le_two_ennreal
        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) Real.normedField
        (fun i =>
          @NonUnitalSeminormedRing.toSeminormedAddCommGroup Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Real
                (@NormedCommRing.toSeminormedCommRing Real Real.normedCommRing))))
        fun i =>
        @InnerProductSpace.toNormedSpace Real Real Real.instRCLike
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Real
                (@NormedCommRing.toSeminormedCommRing Real Real.normedCommRing))))
          (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)))
    MagicFunction.FourierEigenfunctions.a
    (@OfNat.ofNat (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) (nat_lit 0)
      (@Zero.toOfNat0 (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
        (@NegZeroClass.toZero (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
          (@SubNegZeroMonoid.toNegZeroClass
            (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
            (@SubtractionMonoid.toSubNegZeroMonoid
              (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
              (@SubtractionCommMonoid.toSubtractionMonoid
                (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                (@AddCommGroup.toDivisionAddCommMonoid
                  (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                  (@WithLp.instAddCommGroup
                    (@OfNat.ofNat ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                        PiLp.innerProductSpace._proof_1))
                    ((i : Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) → (fun x => Real) i)
                    (@Pi.addCommGroup (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real)
                      fun i => Real.instAddCommGroup))))))))))
  (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))
    (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
      (@Neg.neg Complex Complex.instNeg
        (@OfNat.ofNat Complex (nat_lit 8640) (@instOfNatAtLeastTwo Complex (nat_lit 8640) Complex.instNatCast ⋯)))
      Complex.I)
    ↑Real.pi)
```

六项 ofDecayOn 的显式参数均为 0；上游修复使非负参数上的过渡因子为 1。此修改来自固定上游修复快照，非兼容时自行改动。

root 模块逐字节未改。兼容采用已审查且源模块字节相同的 overlay，或在本快照重复施加相同的冗余 import 删除及已证明恒等式 backport；回执见 repair-evidence/overlay-reuse.json、compat-additions.json。当前闭包的全部修改见 repair-compat-01/changes.patch 和 adapted-source，逐模块 hash 与 proof-hole token 对照见 migration-audit.json；未新增 sorry/admit/axiom。审计不声称历史与目标 Mathlib 全量等价。

环境：Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`；Mathlib 为外部边界。原样尝试保存在 repair-original（cutoff）或 repair-sign-original（b）；成功编译、真实 LeanTrace 和显式参数回执位于 repair-compat-01。图含 335 节点 / 2591 边，排除 theorem/proof-valued 的证明值。工具及原有兼容类型详见本批 TOOL-ISSUES.md。

本版本沿用原负例的同一 informal；标签为 `aligned`，评审入口见 repairs.json 的 review 字段（如有）。上游 fix 不自动意味着 aligned。人工 gold 单独留空。

复现：从仓库根依次运行本批 compile_roots.py --catalog repairs.json --mode compat --attempt NEW --ids SP-A-CUTOFF-FIXED，extract_roots.py --attempt NEW --ids SP-A-CUTOFF-FIXED，audit_explicit.py --attempt NEW --ids SP-A-CUTOFF-FIXED。使用新 attempt 名；已冻结回执不会覆盖。


## SpherePacking/ModularForms/SlashActionAuxil.lean

```diff
--- upstream/SpherePacking/ModularForms/SlashActionAuxil.lean
+++ lean-4.34.1/SpherePacking/ModularForms/SlashActionAuxil.lean
@@ -25,20 +25,25 @@
 local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
 local notation "Γ " n:100 => Gamma n
 
-def α : Γ 2 := ⟨⟨!![1, 2; 0, 1], by simp⟩, by simp; decide⟩
-
-def β : Γ 2 := ⟨⟨!![1, 0; 2, 1], by simp⟩, by simp; decide⟩
-
-def negI : Γ 2 := ⟨⟨!![-1, 0; 0, -1], by simp⟩, by simp⟩
-
-theorem α_eq_T_sq : α = ⟨T ^ 2, by simp [sq, T]; decide⟩ := by ext; simp [α, T, sq]
-
-theorem β_eq_negI_mul_S_mul_α_inv_mul_S : β = negI * S * α⁻¹ * S := by ext; simp [β, S, α, negI]
+def α : Γ 2 := ⟨⟨!![1, 2; 0, 1], by simp⟩, Gamma_mem.mpr (by decide)⟩
+
+def β : Γ 2 := ⟨⟨!![1, 0; 2, 1], by simp⟩, Gamma_mem.mpr (by decide)⟩
+
+def negI : Γ 2 := ⟨⟨!![-1, 0; 0, -1], by simp⟩, Gamma_mem.mpr (by decide)⟩
+
+theorem α_eq_T_sq : α = ⟨T ^ 2, by simp [T]; decide⟩ := by
+  ext i j
+  fin_cases i <;> fin_cases j <;> rfl
+
+theorem β_eq_negI_mul_S_mul_α_inv_mul_S : β = negI * S * α⁻¹ * S := by
+  ext i j
+  fin_cases i <;> fin_cases j <;> rfl
 
 theorem ModularGroup.modular_negI_sq : negI ^ 2 = 1 := by
   ext i j; fin_cases i <;> fin_cases j <;> rfl
 
-theorem ModularGroup.modular_negI_inv : negI⁻¹ = negI := by ext i j; simp [negI]
+theorem ModularGroup.modular_negI_inv : negI⁻¹ = negI := by
+  rw [inv_eq_iff_mul_eq_one, ← sq, modular_negI_sq]
 
 section slash_action
 
@@ -53,10 +58,10 @@
 
 theorem modular_slash_S_apply :
     (f ∣[k] S) z = f (UpperHalfPlane.mk (-z)⁻¹ z.im_inv_neg_coe_pos) * z ^ (-k) := by
-  rw [SL_slash_apply, denom, UpperHalfPlane.modular_S_smul]; simp [S]
+  rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
 
 theorem modular_slash_T_apply : (f ∣[k] T) z = f ((1 : ℝ) +ᵥ z) := by
-  rw [SL_slash_apply, denom, UpperHalfPlane.modular_T_smul]; simp [T]
+  rw [SL_slash_apply, UpperHalfPlane.modular_T_smul, denom_apply]; simp [ModularGroup.coe_T]
 
 end slash_action
```
