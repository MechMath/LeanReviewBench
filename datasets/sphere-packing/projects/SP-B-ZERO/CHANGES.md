# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

## Recorded migration rationale

# SP-B-ZERO：Formal 兼容说明

原 revision：`77cf0a0c104f2e31501eab04d88bbc068d61c169`；root：`MagicFunction.b.SpecialValues.b_zero`。
原路径：`SpherePacking/MagicFunction/b/SpecialValues.lean:25`；源 SHA256：`63ac7110906f89608ea7864f26ed8faba40defc517142f7b2844f15914697add`。
独立 informal 与来源级判断：[SEMANTIC-SCREENING.md](https://github.com/MechMath/PaperLeanBench/blob/964f2d92e71b1b911e568790a7196a6fb7e1250b/experiments/real-project-errors/sphere-packing-01/SEMANTIC-SCREENING.md) 对应小节及 candidates.json pairing。

## 原 Formal 与保留的差异

root 所在模块逐字节未改；以下为目标环境实际 elaborated type（证明正文不参与对齐）：

```lean
MagicFunction.FourierEigenfunctions.b 0 = 0
```

保留 J6 的 +2 系数及 b 的 Schwartz 包装；未应用符号修复。

## 兼容改动与证据

成功尝试 `compat-03`；该目录 `changes.patch` 是本闭包全部修改的精确 diff，`adapted-source/` 是对应有效源，原模块来自固定 sources archive。修改类别见 [TOOL-ISSUES.md](https://github.com/MechMath/PaperLeanBench/blob/964f2d92e71b1b911e568790a7196a6fb7e1250b/experiments/real-project-errors/sphere-packing-01/TOOL-ISSUES.md)；`migration-audit.json` 逐模块记录前后 hash 和 proof-hole token 对照。所有改动均已人工逐 diff 检查；token 数量检查本身不构成语义等价证明。

环境：Lean 4.34.1；Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。原样失败、早期兼容失败及最终成功分别保存在本 root 的 attempt 目录中，不覆盖。Mathlib 保持外部提取边界；未完成历史/现代 Mathlib 全量等价审计。

编译：`python3 compile_roots.py --mode compat --attempt fresh-check --ids SP-B-ZERO`。
抽取：`python3 extract_roots.py --attempt fresh-check --ids SP-B-ZERO`。
显式参数审计：`python3 audit_explicit.py --attempt fresh-check --ids SP-B-ZERO`。
以上脚本路径均相对于本批目录；从仓库根执行时加完整批次路径。构建缓存可在 /tmp，来源/overlay/raw/回执均持久归档。

最终成功记录：`compat-03/status.json` 和 `compat-03/compile.log`；真实 LeanTrace：`compat-03/raw.json`、`graph.json`、`extraction.json`、`extraction-receipt.json`；另有 `raw-explicit.json` 及显式打印回执。
导出 273 节点、1658 条边，root/项目可达定义/外部边界已核对；未遍历 theorem/proof-valued 的证明值。原有 sorry 保持原位，未增加新 proof holes。

技术验证完成。当前标签为 `misaligned`；独立评审层见 candidates.json 的 review 字段（如有），人工 gold 单独记录，不由本重建脚本决定。


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
@@ -10,6 +10,11 @@
 -/
 
 @[expose] public section
+
+-- Compatibility lemma absent from the fixed Mathlib version; proof only.
+lemma Complex.norm_exp_mul_I (z : ℂ) : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
+  rw [Complex.norm_exp]
+  simp
 
 open scoped Real MatrixGroups ModularForm
 open UpperHalfPlane hiding I
```
