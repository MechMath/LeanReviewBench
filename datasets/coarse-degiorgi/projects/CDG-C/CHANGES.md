# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

Only proof-local elaboration compatibility in SelectionAdapters changes; root statements and reachable data definitions are retained.

## CoarseDeGiorgi/Harnack/WeakHarnack/SelectionAdapters.lean

```diff
--- upstream/CoarseDeGiorgi/Harnack/WeakHarnack/SelectionAdapters.lean
+++ lean-4.34.1/CoarseDeGiorgi/Harnack/WeakHarnack/SelectionAdapters.lean
@@ -145,6 +145,7 @@
     ENNReal.ofReal_inv_of_pos (by positivity)]
   norm_num
 
+set_option backward.isDefEq.respectTransparency false in
 private theorem sourceSampledResponse_eq_statement {d : ℕ} [NeZero d]
     (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
     (k : ℕ) (τ : ℝ) (hτ : τ ∈ Ioo (1 / 2 : ℝ) 1) :
@@ -155,7 +156,6 @@
       (Finset.univ : Finset (SimplexIndex d k)) := by
     ext η
     simp [SimplexIndex]
-  dsimp only [SimplexIndex] at hattach ⊢
   unfold Selection.sourceSampledResponse Selection.sampledMaximum
   rw [Finset.sup_eq_iSup, hattach]
   simp only [Finset.mem_univ, iSup_true]
```
