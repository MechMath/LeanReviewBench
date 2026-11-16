# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

## Recorded migration rationale

# SP-LP：Formal 兼容说明

原 revision：`77cf0a0c104f2e31501eab04d88bbc068d61c169`；root：`LinearProgrammingBound`。
原路径：`SpherePacking/CohnElkies/LPBound.lean:642`；源 SHA256：`9dfad9d67d0696860f908ce86f3a57302c63f82817d51769ef53ca7be9af28af`。
独立 informal 与来源级判断：[SEMANTIC-SCREENING.md](https://github.com/MechMath/PaperLeanBench/blob/964f2d92e71b1b911e568790a7196a6fb7e1250b/experiments/real-project-errors/sphere-packing-01/SEMANTIC-SCREENING.md) 对应小节及 candidates.json pairing。

## 原 Formal 与保留的差异

root 所在模块逐字节未改；以下为目标环境实际 elaborated type（证明正文不参与对齐）：

```lean
∀ {d : ℕ} {f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ},
  f ≠ 0 →
    (∀ (x : EuclideanSpace ℝ (Fin d)), ↑(f x).re = f x) →
      (∀ (x : EuclideanSpace ℝ (Fin d)), ↑((FourierTransform.fourier f) x).re = (FourierTransform.fourier f) x) →
        (∀ (x : EuclideanSpace ℝ (Fin d)), ‖x‖ ≥ 1 → (f x).re ≤ 0) →
          (∀ (x : EuclideanSpace ℝ (Fin d)), ((FourierTransform.fourier f) x).re ≥ 0) →
            0 < d →
              Summable ⇑f →
                SpherePackingConstant d ≤
                  ↑(f 0).re.toNNReal / ↑(FourierTransform.fourier (⇑f) 0).re.toNNReal *
                    MeasureTheory.volume (Metric.ball 0 (1 / 2))
```

保留对全部欧氏空间点的 Summable f，未换成积分或格点求和。

## 兼容改动与证据

成功尝试 `compat-01`；该目录 `changes.patch` 是本闭包全部修改的精确 diff，`adapted-source/` 是对应有效源，原模块来自固定 sources archive。修改类别见 [TOOL-ISSUES.md](https://github.com/MechMath/PaperLeanBench/blob/964f2d92e71b1b911e568790a7196a6fb7e1250b/experiments/real-project-errors/sphere-packing-01/TOOL-ISSUES.md)；`migration-audit.json` 逐模块记录前后 hash 和 proof-hole token 对照。所有改动均已人工逐 diff 检查；token 数量检查本身不构成语义等价证明。

环境：Lean 4.34.1；Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。原样失败、早期兼容失败及最终成功分别保存在本 root 的 attempt 目录中，不覆盖。Mathlib 保持外部提取边界；未完成历史/现代 Mathlib 全量等价审计。

编译：`python3 compile_roots.py --mode compat --attempt fresh-check --ids SP-LP`。
抽取：`python3 extract_roots.py --attempt fresh-check --ids SP-LP`。
显式参数审计：`python3 audit_explicit.py --attempt fresh-check --ids SP-LP`。
以上脚本路径均相对于本批目录；从仓库根执行时加完整批次路径。构建缓存可在 /tmp，来源/overlay/raw/回执均持久归档。

最终成功记录：`compat-01/status.json` 和 `compat-01/compile.log`；真实 LeanTrace：`compat-01/raw.json`、`graph.json`、`extraction.json`、`extraction-receipt.json`；另有 `raw-explicit.json` 及显式打印回执。
导出 187 节点、368 条边，root/项目可达定义/外部边界已核对；未遍历 theorem/proof-valued 的证明值。原有 sorry 保持原位，未增加新 proof holes。

技术验证完成。当前标签为 `misaligned`；独立评审层见 candidates.json 的 review 字段（如有），人工 gold 单独记录，不由本重建脚本决定。


## SpherePacking/Basic/PeriodicPacking.lean

```diff
--- upstream/SpherePacking/Basic/PeriodicPacking.lean
+++ lean-4.34.1/SpherePacking/Basic/PeriodicPacking.lean
@@ -570,7 +570,7 @@
   nullMeasurableSet := hD_measurable.nullMeasurableSet
   ae_covers := Filter.Eventually.of_forall fun x ↦ (hD_unique_covers x).exists
   aedisjoint := by
-    apply pairwise_aedisjoint_of_aedisjoint_forall_ne_zero
+    apply MeasureTheory.Measure.pairwise_aedisjoint_of_aedisjoint_forall_ne_zero
     · intro g hg
       apply Disjoint.aedisjoint
       rw [Set.disjoint_iff]
@@ -843,7 +843,7 @@
     simp only [max_le_iff, and_imp]
     intro k' hk₀ hk₁
     have := hk k' hk₁
-    rwa [sub_zero, ofReal_one, one_rpow, ←one_div, one_sub_div, add_sub_cancel_right,
+    rwa [sub_zero, ofReal_one, one_rpow, ←one_div, one_sub_div (by linarith : k' + 1 ≠ 0), add_sub_cancel_right,
       ENNReal.ofReal_rpow_of_nonneg] at this
     · positivity
     · positivity
```
