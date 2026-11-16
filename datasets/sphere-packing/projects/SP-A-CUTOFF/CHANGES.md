# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

## Recorded migration rationale

# SP-A-CUTOFF：Formal 兼容说明

原 revision：`8dbcc8c87a6e55b7048ffdb474fcbead5c2d4ba1`；root：`MagicFunction.a.SpecialValues.a_zero`。
原路径：`SpherePacking/MagicFunction/a/SpecialValues.lean:25`；源 SHA256：`3b8be55d7cdf8f287415251aab24a911b9b4b3c87940d39f7b19c42c432b9afa`。
独立 informal 与来源级判断：[SEMANTIC-SCREENING.md](https://github.com/MechMath/PaperLeanBench/blob/964f2d92e71b1b911e568790a7196a6fb7e1250b/experiments/real-project-errors/sphere-packing-01/SEMANTIC-SCREENING.md) 对应小节及 candidates.json pairing。

## 原 Formal 与保留的差异

root 所在模块逐字节未改；以下为目标环境实际 elaborated type（证明正文不参与对齐）：

```lean
MagicFunction.FourierEigenfunctions.a 0 = -8640 * Complex.I / ↑Real.pi
```

保留历史 ofDecayOn (a := 1) 和 bundled a 的平方范数提升；未应用 #485。

## 兼容改动与证据

成功尝试 `compat-02`；该目录 `changes.patch` 是本闭包全部修改的精确 diff，`adapted-source/` 是对应有效源，原模块来自固定 sources archive。修改类别见 [TOOL-ISSUES.md](https://github.com/MechMath/PaperLeanBench/blob/964f2d92e71b1b911e568790a7196a6fb7e1250b/experiments/real-project-errors/sphere-packing-01/TOOL-ISSUES.md)；`migration-audit.json` 逐模块记录前后 hash 和 proof-hole token 对照。所有改动均已人工逐 diff 检查；token 数量检查本身不构成语义等价证明。

环境：Lean 4.34.1；Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。原样失败、早期兼容失败及最终成功分别保存在本 root 的 attempt 目录中，不覆盖。Mathlib 保持外部提取边界；未完成历史/现代 Mathlib 全量等价审计。

编译：`python3 compile_roots.py --mode compat --attempt fresh-check --ids SP-A-CUTOFF`。
抽取：`python3 extract_roots.py --attempt fresh-check --ids SP-A-CUTOFF`。
显式参数审计：`python3 audit_explicit.py --attempt fresh-check --ids SP-A-CUTOFF`。
以上脚本路径均相对于本批目录；从仓库根执行时加完整批次路径。构建缓存可在 /tmp，来源/overlay/raw/回执均持久归档。

最终成功记录：`compat-02/status.json` 和 `compat-02/compile.log`；真实 LeanTrace：`compat-02/raw.json`、`graph.json`、`extraction.json`、`extraction-receipt.json`；另有 `raw-explicit.json` 及显式打印回执。
导出 335 节点、2615 条边，root/项目可达定义/外部边界已核对；未遍历 theorem/proof-valued 的证明值。原有 sorry 保持原位，未增加新 proof holes。

技术验证完成。当前标签为 `misaligned`；独立评审层见 candidates.json 的 review 字段（如有），人工 gold 单独记录，不由本重建脚本决定。


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
