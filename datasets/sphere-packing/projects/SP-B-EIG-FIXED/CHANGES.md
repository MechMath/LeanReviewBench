# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

## Recorded migration rationale

# SP-B-EIG-FIXED：修复版 Formal 与兼容说明

原负例：`SP-B-EIG`；修复快照：`af2a2ac5002c62b9cbaab018c163e150dc960a4b`。
root：`MagicFunction.b.Fourier.eig_b`；源路径：`SpherePacking/MagicFunction/b/Eigenfunction.lean:70`。
上游 PR #504；修复提交 `af2a2ac5002c62b9cbaab018c163e150dc960a4b`。

## 固定 Formal

```lean
@Eq
  (@SchwartzMap (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) Complex
    (@PiLp.normedAddCommGroup
      (@OfNat.ofNat ENNReal (nat_lit 2)
        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
          (@AddMonoidWithOne.toNatCast ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
          PiLp.innerProductSpace._proof_1))
      (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fact_one_le_two_ennreal
      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) fun i => Real.normedAddCommGroup)
    (@InnerProductSpace.toNormedSpace Real
      (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) Real.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
        (@PiLp.normedAddCommGroup
          (@OfNat.ofNat ENNReal (nat_lit 2)
            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
              (@AddMonoidWithOne.toNatCast ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
              PiLp.innerProductSpace._proof_1))
          (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fact_one_le_two_ennreal
          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) fun i => Real.normedAddCommGroup))
      (@PiLp.innerProductSpace Real Real.instRCLike (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real)
        (fun i => Real.normedAddCommGroup) fun i => @RCLike.toInnerProductSpaceReal Real Real.instRCLike))
    Complex.instNormedAddCommGroup
    (@NormedSpace.complexToReal Complex
      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
      (@InnerProductSpace.toNormedSpace Complex Complex Complex.instRCLike
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
              (@NormedCommRing.toSeminormedCommRing Complex
                (@NormedField.toNormedCommRing Complex Complex.instNormedField)))))
        (@RCLike.innerProductSpace Complex Complex.instRCLike))))
  (@FourierTransform.fourier
    (@SchwartzMap (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) Complex
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
        instInnerProductSpaceRealComplex))
    (@SchwartzMap (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) Complex
      (@PiLp.normedAddCommGroup
        (@OfNat.ofNat ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
            PiLp.innerProductSpace._proof_1))
        (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fact_one_le_two_ennreal
        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) fun i => Real.normedAddCommGroup)
      (@InnerProductSpace.toNormedSpace Real
        (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup
          (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
          (@PiLp.normedAddCommGroup
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                PiLp.innerProductSpace._proof_1))
            (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fact_one_le_two_ennreal
            (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) fun i => Real.normedAddCommGroup))
        (@PiLp.innerProductSpace Real Real.instRCLike (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real)
          (fun i => Real.normedAddCommGroup) fun i => @RCLike.toInnerProductSpaceReal Real Real.instRCLike))
      Complex.instNormedAddCommGroup
      (@NormedSpace.complexToReal Complex
        (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
        (@InnerProductSpace.toNormedSpace Complex Complex Complex.instRCLike
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                (@NormedCommRing.toSeminormedCommRing Complex
                  (@NormedField.toNormedCommRing Complex Complex.instNormedField)))))
          (@RCLike.innerProductSpace Complex Complex.instRCLike))))
    (@SchwartzMap.instFourierTransform Complex Complex.instNormedAddCommGroup
      (@InnerProductSpace.toNormedSpace Complex Complex Complex.instRCLike
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
              (@NormedCommRing.toSeminormedCommRing Complex
                (@NormedField.toNormedCommRing Complex Complex.instNormedField)))))
        (@RCLike.innerProductSpace Complex Complex.instRCLike))
      (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (@PiLp.normedAddCommGroup
        (@OfNat.ofNat ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
            PiLp.innerProductSpace._proof_1))
        (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fact_one_le_two_ennreal
        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) fun i => Real.normedAddCommGroup)
      (@PiLp.innerProductSpace Real Real.instRCLike (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real)
        (fun i => Real.normedAddCommGroup) fun i => @RCLike.toInnerProductSpaceReal Real Real.instRCLike)
      ⋯
      (@WithLp.measurableSpace
        (@OfNat.ofNat ENNReal (nat_lit 2)
          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
            (@AddMonoidWithOne.toNatCast ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
            PiLp.innerProductSpace._proof_1))
        ((i : Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) → (fun x => Real) i)
        (@MeasurableSpace.pi (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (fun x => Real) fun a =>
          Real.measurableSpace))
      ⋯)
    MagicFunction.FourierEigenfunctions.b)
  (@Neg.neg
    (@SchwartzMap (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) Complex
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
        instInnerProductSpaceRealComplex))
    (@SchwartzMap.instNeg (EuclideanSpace Real (Fin (@OfNat.ofNat Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) Complex
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
        instInnerProductSpaceRealComplex))
    MagicFunction.FourierEigenfunctions.b)
```

J6 系数为 −2，来自上游修复提交；保留固定论文 (52) 的约定。采用原始符号修复提交，保留与其实际父提交及原负例快照的完整差异。

root 模块逐字节未改。兼容采用已审查且源模块字节相同的 overlay，或在本快照重复施加相同的冗余 import 删除及已证明恒等式 backport；回执见 repair-evidence/overlay-reuse.json、compat-additions.json。当前闭包的全部修改见 repair-sign-compat-02/changes.patch 和 adapted-source，逐模块 hash 与 proof-hole token 对照见 migration-audit.json；未新增 sorry/admit/axiom。审计不声称历史与目标 Mathlib 全量等价。

环境：Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`；Mathlib 为外部边界。原样尝试保存在 repair-original（cutoff）或 repair-sign-original（b）；成功编译、真实 LeanTrace 和显式参数回执位于 repair-sign-compat-02。图含 291 节点 / 1687 边，排除 theorem/proof-valued 的证明值。工具及原有兼容类型详见本批 TOOL-ISSUES.md。

本版本沿用原负例的同一 informal；标签为 `aligned`，评审入口见 repairs.json 的 review 字段（如有）。上游 fix 不自动意味着 aligned。人工 gold 单独留空。

复现：从仓库根依次运行本批 compile_roots.py --catalog repairs.json --mode compat --attempt NEW --ids SP-B-EIG-FIXED，extract_roots.py --attempt NEW --ids SP-B-EIG-FIXED，audit_explicit.py --attempt NEW --ids SP-B-EIG-FIXED。使用新 attempt 名；已冻结回执不会覆盖。


## SpherePacking/ForMathlib/RadialSchwartz/Multidimensional.lean

```diff
--- upstream/SpherePacking/ForMathlib/RadialSchwartz/Multidimensional.lean
+++ lean-4.34.1/SpherePacking/ForMathlib/RadialSchwartz/Multidimensional.lean
@@ -9,7 +9,6 @@
 public import Mathlib.Analysis.InnerProductSpace.Calculus
 public import Mathlib.Algebra.Order.Star.Real
 public import Mathlib.Analysis.Calculus.ContDiff.Bounds
-public import Mathlib.Analysis.Normed.Group.RadialFunction
 public import SpherePacking.ForMathlib.RadialSchwartz.SchwartzMap
 public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
 
@@ -18,6 +17,13 @@
 -/
 
 @[expose] public section
+
+-- Compatibility: same IsRadial definition as the archived historical project Basic module.
+namespace Function
+/-- A function is radial if it factors through its norm. -/
+def IsRadial {E F : Type*} [Norm E] (f : E → F) : Prop :=
+  f.FactorsThrough (‖·‖ : E → ℝ)
+end Function
 
 open SchwartzMap Function RCLike
 
@@ -37,11 +43,12 @@
   nlinarith
 
 /-- The multidimensional lift `x ↦ f (‖x‖ ^ 2)` of a real Schwartz function is radial. -/
-@[fun_prop]
 theorem isRadial_schwartzMap_multidimensional_of_schwartzMap_real :
     IsRadial (schwartzMap_multidimensional_of_schwartzMap_real F f) := by
-  simp only [schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
-  fun_prop
+  intro x y h
+  change f (‖x‖ ^ 2) = f (‖y‖ ^ 2)
+  change ‖x‖ = ‖y‖ at h
+  rw [h]
 
 @[fun_prop]
 theorem contDiff_ofReal {n} : ContDiff ℝ n Complex.ofReal :=
```

## SpherePacking/ModularForms/DimensionFormulas.lean

```diff
--- upstream/SpherePacking/ModularForms/DimensionFormulas.lean
+++ lean-4.34.1/SpherePacking/ModularForms/DimensionFormulas.lean
@@ -1,6 +1,5 @@
 module
 
-public import Mathlib.Algebra.Order.Star.Rat
 public import Mathlib.LinearAlgebra.Dimension.Localization
 public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
 public import SpherePacking.ModularForms.Eisenstein
```

## SpherePacking/ModularForms/JacobiTheta/Basic.lean

```diff
--- upstream/SpherePacking/ModularForms/JacobiTheta/Basic.lean
+++ lean-4.34.1/SpherePacking/ModularForms/JacobiTheta/Basic.lean
@@ -10,6 +10,12 @@
 -/
 
 @[expose] public section
+
+-- Compatibility lemma absent from fixed Mathlib; same identity as the prior batch.
+lemma Complex.norm_exp_mul_I (z : ℂ) : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
+  rw [Complex.norm_exp]
+  simp
+
 
 open scoped Real MatrixGroups ModularForm
 open UpperHalfPlane hiding I
```
