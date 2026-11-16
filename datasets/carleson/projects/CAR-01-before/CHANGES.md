# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

## Recorded migration rationale

# Formal migration: metric_carleson at 0138d636eed1475ea5e848ef6cf4b141636056cc

Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Reproduce with `python3 migrate_212.py 0138d636eed1475ea5e848ef6cf4b141636056cc` from `carleson-01`. Evidence: `technical/0138d636eed1475ea5e848ef6cf4b141636056cc/migration-212/`: full compile log, status, raw LeanTrace graph, extraction log, exact compatibility patch and adapted source. Original frozen source is untouched.

The root source is byte-identical. In particular, the historical `nontangentialOperator … |>.toReal` bounded-strong-type assumption is retained in the pre-fix snapshot and its removal retained in the post-fix snapshot. No root assumptions, conclusions, quantifiers, constants, or operator definitions are strengthened to force compilation.

Historical ENorm classes are copied under `Legacy212_` names. Their original bundled topology and ENorm fields remain unchanged. A one-way bridge from the legacy continuous norm class to the modern class exists **locally in WeakType only**; it projects the same norm/topology and does not export a new global instance. Historical norm and membership definitions are retained in `Carleson.Legacy212Norm`: `legacy212Norm` uses the original exponent-zero/infinity/finite piecewise formula, and `Legacy212MemLp` is the old measurability-and-finiteness conjunction. The helper proves equality with modern eLpNorm only under the original measurable hypothesis; it does not identify both norms on arbitrary functions. See also the parent `migration/LegacyNormBridge.lean` for the bounded-strong-type contract equivalence, not a blanket replacement of all boundary constants.

`Real.IsConjExponent` is copied with its two exact fields (`one_lt : 1 < p`, `inv_add_inv_conj : p⁻¹ + q⁻¹ = 1`) from the historical Mathlib file `historical-boundary/c083085d-ConjExponents.lean`; it is not silently replaced by a current predicate.

Compatibility edits otherwise rename collisions and moved APIs, modernize sum notation/imports, and repair proof elaboration. `WithFunctionDistance` keeps its original body `Θ X` but is marked reducible to restore old definitional unfolding. `CompatibleFunctions.eq_zero` explicitly spells out the old coercion as `coeΘ f o`; the function and quantified types are the same. `BoundedSMul` is renamed `IsBoundedSMul`. The original layercake conclusion `ENNReal.ofReal (p + 1)⁻¹` is unchanged: the proof explicitly uses `ENNReal.ofReal_inv_of_pos` under its pre-existing `-1 < p` assumption.

Every changed theorem header is recorded in `proof-header-changes.json` alongside its original text (83 entries). These changes are API/class/local-name substitutions and finite-sum notation, with no added hypotheses. Definition/class changes are visible in the full compatibility patch. Existing sorry occurrences are preserved per module; no new sorry/proof stub is introduced. Historical root proof sorry remains a proof-completeness limitation, separate from statement alignment. LeanTrace follows statement types and definition values, and does not traverse theorem proof values.


## Carleson/ToMathlib/MeasureReal.lean

```diff
--- upstream/Carleson/ToMathlib/MeasureReal.lean
+++ lean-4.34.1/Carleson/ToMathlib/MeasureReal.lean
@@ -1,3 +1,4 @@
+import Mathlib.Tactic
 import Mathlib.MeasureTheory.Measure.Prod
 import Mathlib.Tactic.Finiteness
 
@@ -17,7 +18,7 @@
 There are certainly many missing lemmas. The idea is to add the missing ones as we notice that they
 would be useful while doing the project.
 
-I haven't transferred any lemma involving infinite sums, as summability issues are really
+I haven't transferred any lemma carleson_involving infinite sums, as summability issues are really
 more painful with reals than nonnegative extended reals. I don't expect we will need them in the
 project, but we should probably add them back in the long run if they turn out to be useful.
 -/
@@ -29,31 +30,31 @@
 section aux_lemmas
 
 @[simp]
-lemma Finset.sum_measure_singleton {S : Type*} {s : Finset S} {_ : MeasurableSpace S}
+lemma Finset.carleson_sum_measure_singleton {S : Type*} {s : Finset S} {_ : MeasurableSpace S}
     [MeasurableSingletonClass S] (μ : Measure S) :
-    ∑ x in s, μ {x} = μ s := by
-  change ∑ x in s, μ (id ⁻¹' {x}) = _
+    ∑ x ∈ s, μ {x} = μ s := by
+  change ∑ x ∈ s, μ (id ⁻¹' {x}) = _
   rw [sum_measure_preimage_singleton]
   · simp
   · simp
 
 @[simp]
-lemma Finset.sum_toReal_measure_singleton {S : Type*} {s : Finset S} {_ : MeasurableSpace S}
+lemma Finset.carleson_sum_toReal_measure_singleton {S : Type*} {s : Finset S} {_ : MeasurableSpace S}
     [MeasurableSingletonClass S] (μ : Measure S) [IsFiniteMeasure μ] :
-    ∑ x in s, (μ {x}).toReal = (μ s).toReal := by
+    ∑ x ∈ s, (μ {x}).toReal = (μ s).toReal := by
   rw [← ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
   simp
 
 -- probably don't need this version but it was stated previously and will need to search for and
 -- eliminate any explicit uses
-lemma sum_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
+lemma carleson_sum_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
     [MeasurableSingletonClass S] (μ : Measure S) :
     ∑ x, μ {x} = μ Set.univ := by
   simp
 
 -- probably don't need this version but it was stated previously and will need to search for and
 -- eliminate any explicit uses
-lemma sum_toReal_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
+lemma carleson_sum_toReal_measure_singleton {S : Type*} [Fintype S] {_ : MeasurableSpace S}
     [MeasurableSingletonClass S] (μ : Measure S) [IsFiniteMeasure μ] :
     ∑ x : S, (μ {x}).toReal = (μ Set.univ).toReal := by
   simp
@@ -65,399 +66,397 @@
 variable {α : Type*} {β : Type*} {_ : MeasurableSpace α} (μ : Measure α)
 
 /-- The real-valued version of a measure. Maps infinite measure sets to zero. Use as `μ.real s`. -/
-protected def Measure.real (s : Set α) : ℝ :=
+protected def Measure.carlesonReal (s : Set α) : ℝ :=
   (μ s).toReal
 
-theorem measureReal_def (s : Set α) : μ.real s = (μ s).toReal := rfl
+theorem carleson_measureReal_def (s : Set α) : μ.real s = (μ s).toReal := rfl
 
 /-- The real-valued version of a measure. Maps infinite measure sets to zero. Use as `μ.real s`. -/
-protected def Measure.nnreal (s : Set α) : ℝ≥0 :=
+protected def Measure.carlesonNnreal (s : Set α) : ℝ≥0 :=
   (μ s).toNNReal
 
-theorem measureNNReal_def (s : Set α) : μ.nnreal s = (μ s).toNNReal := rfl
-
-theorem measureNNReal_toReal (s : Set α) : (μ.nnreal s).toReal = μ.real s := rfl
-
-theorem measureNNReal_val (s : Set α) : (μ.nnreal s).val = μ.real s := rfl
+theorem carleson_measureNNReal_def (s : Set α) : μ.carlesonNnreal s = (μ s).toNNReal := rfl
+
+theorem carleson_measureNNReal_toReal (s : Set α) : (μ.carlesonNnreal s).toReal = μ.real s := rfl
+
+theorem carleson_measureNNReal_val (s : Set α) : (μ.carlesonNnreal s).val = μ.real s := rfl
 
 variable {μ}
 variable {s s₁ s₂ t : Set α}
 
 section move_to_MeasureSpace.lean
 
-theorem measure_ne_top_of_subset (h : s ⊆ t) (ht : μ t ≠ ∞) : μ s ≠ ∞ :=
+theorem carleson_measure_ne_top_of_subset (h : s ⊆ t) (ht : μ t ≠ ∞) : μ s ≠ ∞ :=
   (measure_lt_top_of_subset h ht).ne
 
-theorem measure_diff_eq_top (hs : μ s = ∞) (ht : μ t ≠ ∞) : μ (s \ t) = ∞ := by
+theorem carleson_measure_diff_eq_top (hs : μ s = ∞) (ht : μ t ≠ ∞) : μ (s \ t) = ∞ := by
   contrapose! hs
   exact ((measure_mono (subset_diff_union s t)).trans_lt
     ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs.lt_top, ht.lt_top⟩))).ne
 
-theorem measure_symmDiff_eq_top (hs : μ s ≠ ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞ :=
-  measure_mono_top subset_union_right (measure_diff_eq_top ht hs)
+theorem carleson_measure_symmDiff_eq_top (hs : μ s ≠ ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞ :=
+  measure_mono_top subset_union_right (carleson_measure_diff_eq_top ht hs)
 
 end move_to_MeasureSpace.lean
 
-theorem measureReal_eq_zero_iff (h : μ s ≠ ∞ := by finiteness) :
+theorem carleson_measureReal_eq_zero_iff (h : μ s ≠ ∞ := by finiteness) :
     μ.real s = 0 ↔ μ s = 0 := by
   rw [Measure.real, ENNReal.toReal_eq_zero_iff]
   exact or_iff_left h
 
-@[simp] theorem measureReal_zero (s : Set α) : (0 : Measure α).real s = 0 := rfl
-
-@[simp] theorem measureReal_nonneg : 0 ≤ μ.real s := ENNReal.toReal_nonneg
-
-@[simp] theorem measureReal_empty : μ.real ∅ = 0 := by simp [Measure.real]
-
-@[simp] theorem IsProbabilityMeasure.measureReal_univ [IsProbabilityMeasure μ] :
+@[simp] theorem carleson_measureReal_zero (s : Set α) : (0 : Measure α).real s = 0 := rfl
+
+@[simp] theorem carleson_measureReal_nonneg : 0 ≤ μ.real s := ENNReal.toReal_nonneg
+
+@[simp] theorem carleson_measureReal_empty : μ.real ∅ = 0 := by simp [Measure.real]
+
+@[simp] theorem IsProbabilityMeasure.carleson_measureReal_univ [IsProbabilityMeasure μ] :
     μ.real Set.univ = 1 := by
   simp [Measure.real]
 
-theorem measureReal_univ_pos [IsFiniteMeasure μ] [NeZero μ] : 0 < μ.real Set.univ :=
+theorem carleson_measureReal_univ_pos [IsFiniteMeasure μ] [NeZero μ] : 0 < μ.real Set.univ :=
   ENNReal.toReal_pos (NeZero.ne (μ Set.univ)) (measure_ne_top μ univ)
 
-theorem measureReal_univ_ne_zero [IsFiniteMeasure μ] [NeZero μ] : μ.real Set.univ ≠ 0 :=
-  measureReal_univ_pos.ne'
-
-theorem nonempty_of_measureReal_ne_zero (h : μ.real s ≠ 0) : s.Nonempty :=
-  nonempty_iff_ne_empty.2 fun h' ↦ h <| h'.symm ▸ measureReal_empty
-
-@[simp] theorem measureReal_smul_apply (c : ℝ≥0∞) : (c • μ).real s = c.toReal • μ.real s := by
-  rw [measureReal_def, smul_apply, smul_eq_mul, ENNReal.toReal_mul]
+theorem carleson_measureReal_univ_ne_zero [IsFiniteMeasure μ] [NeZero μ] : μ.real Set.univ ≠ 0 :=
+  carleson_measureReal_univ_pos.ne'
+
+theorem carleson_nonempty_of_measureReal_ne_zero (h : μ.real s ≠ 0) : s.Nonempty :=
+  nonempty_iff_ne_empty.2 fun h' ↦ h <| h'.symm ▸ carleson_measureReal_empty
+
+@[simp] theorem carleson_measureReal_smul_apply (c : ℝ≥0∞) : (c • μ).real s = c.toReal • μ.real s := by
+  rw [carleson_measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
   rfl
 
-theorem map_measureReal_apply [MeasurableSpace β] {f : α → β} (hf : Measurable f)
+theorem carleson_map_measureReal_apply [MeasurableSpace β] {f : α → β} (hf : Measurable f)
     {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.real (f ⁻¹' s) := by
-  rw [measureReal_def, map_apply hf hs]
+  rw [carleson_measureReal_def, map_apply hf hs]
   rfl
 
-@[gcongr] theorem measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
+@[gcongr] theorem carleson_measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
     μ.real s₁ ≤ μ.real s₂ :=
   ENNReal.toReal_mono h₂ (measure_mono h)
 
-theorem measureReal_mono_null (h : s₁ ⊆ s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ ≠ ∞ := by finiteness) :
+theorem carleson_measureReal_mono_null (h : s₁ ⊆ s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ ≠ ∞ := by finiteness) :
     μ.real s₁ = 0 := by
-  rw [measureReal_eq_zero_iff h'₂] at h₂
+  rw [carleson_measureReal_eq_zero_iff h'₂] at h₂
   simp [Measure.real, measure_mono_null h h₂]
 
-theorem measureReal_le_measureReal_union_left (h : μ t ≠ ∞ := by finiteness) :
+theorem carleson_measureReal_le_measureReal_union_left (h : μ t ≠ ∞ := by finiteness) :
     μ.real s ≤ μ.real (s ∪ t) := by
   rcases eq_top_or_lt_top (μ s) with hs|hs
   · simp [Measure.real, hs]
-  · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne
-
-theorem measureReal_le_measureReal_union_right (h : μ s ≠ ∞ := by finiteness) :
+  · exact carleson_measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne
+
+theorem carleson_measureReal_le_measureReal_union_right (h : μ s ≠ ∞ := by finiteness) :
     μ.real t ≤ μ.real (s ∪ t) := by
   rw [union_comm]
-  exact measureReal_le_measureReal_union_left h
-
-theorem measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ ∪ s₂) ≤ μ.real s₁ + μ.real s₂ := by
+  exact carleson_measureReal_le_measureReal_union_left h
+
+theorem carleson_measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ ∪ s₂) ≤ μ.real s₁ + μ.real s₂ := by
   rcases eq_top_or_lt_top (μ (s₁ ∪ s₂)) with h|h
-  · simp only [Measure.real, h, ENNReal.top_toReal]
+  · simp only [Measure.real, h, ENNReal.toReal_top]
     exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
-  · have A : μ s₁ ≠ ∞ := measure_ne_top_of_subset subset_union_left h.ne
-    have B : μ s₂ ≠ ∞ := measure_ne_top_of_subset subset_union_right h.ne
+  · have A : μ s₁ ≠ ∞ := carleson_measure_ne_top_of_subset subset_union_left h.ne
+    have B : μ s₂ ≠ ∞ := carleson_measure_ne_top_of_subset subset_union_right h.ne
     simp only [Measure.real, ← ENNReal.toReal_add A B]
     exact ENNReal.toReal_mono (by simp [A, B]) (measure_union_le _ _)
 
-theorem measureReal_biUnion_finset_le (s : Finset β) (f : β → Set α) :
-    μ.real (⋃ b ∈ s, f b) ≤ ∑ p in s, μ.real (f p) := by
+theorem carleson_measureReal_biUnion_finset_le (s : Finset β) (f : β → Set α) :
+    μ.real (⋃ b ∈ s, f b) ≤ ∑ p ∈ s, μ.real (f p) := by
   classical
   induction' s using Finset.induction_on with x s hx IH
   · simp
   · simp only [hx, Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,
       Finset.sum_insert]
-    exact (measureReal_union_le _ _).trans (by gcongr)
-
-theorem measureReal_iUnion_fintype_le [Fintype β] (f : β → Set α) :
+    exact (carleson_measureReal_union_le _ _).trans (by gcongr)
+
+theorem carleson_measureReal_iUnion_fintype_le [Fintype β] (f : β → Set α) :
     μ.real (⋃ b, f b) ≤ ∑ p, μ.real (f p) := by
-  convert measureReal_biUnion_finset_le Finset.univ f
+  convert carleson_measureReal_biUnion_finset_le Finset.univ f
   simp
 
-theorem measureReal_iUnion_fintype [Fintype β] {f : β → Set α} (hn : Pairwise (Disjoint on f))
+theorem carleson_measureReal_iUnion_fintype [Fintype β] {f : β → Set α} (hn : Pairwise (Disjoint on f))
     (h : ∀ i, MeasurableSet (f i)) (h' : ∀ i, μ (f i) ≠ ∞ := by finiteness) :
     μ.real (⋃ b, f b) = ∑ p, μ.real (f p) := by
-  rw [measureReal_def, measure_iUnion hn h, tsum_fintype, ENNReal.toReal_sum (fun i _hi ↦ h' i)]
+  rw [carleson_measureReal_def, measure_iUnion hn h, tsum_fintype, ENNReal.toReal_sum (fun i _hi ↦ h' i)]
   rfl
 
-theorem measureReal_union_null (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0) :
+theorem carleson_measureReal_union_null (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0) :
     μ.real (s₁ ∪ s₂) = 0 :=
-  le_antisymm ((measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])) measureReal_nonneg
+  le_antisymm ((carleson_measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])) carleson_measureReal_nonneg
 
 @[simp]
-theorem measureReal_union_null_iff
+theorem carleson_measureReal_union_null_iff
     (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
     μ.real (s₁ ∪ s₂) = 0 ↔ μ.real s₁ = 0 ∧ μ.real s₂ = 0 :=
-  ⟨fun h ↦ ⟨measureReal_mono_null subset_union_left h (measure_union_ne_top h₁ h₂),
-      measureReal_mono_null subset_union_right h (measure_union_ne_top h₁ h₂)⟩,
-        fun h ↦ measureReal_union_null h.1 h.2⟩
+  ⟨fun h ↦ ⟨carleson_measureReal_mono_null subset_union_left h (measure_union_ne_top h₁ h₂),
+      carleson_measureReal_mono_null subset_union_right h (measure_union_ne_top h₁ h₂)⟩,
+        fun h ↦ carleson_measureReal_union_null h.1 h.2⟩
 
 /-- If two sets are equal modulo a set of measure zero, then `μ.real s = μ.real t`. -/
-theorem measureReal_congr (H : s =ᵐ[μ] t) : μ.real s = μ.real t := by
+theorem carleson_measureReal_congr (H : s =ᵐ[μ] t) : μ.real s = μ.real t := by
   simp [Measure.real, measure_congr H]
 
-theorem measureReal_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ)
+theorem carleson_measureReal_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ)
     (h : μ s ≠ ∞ := by finiteness) :
     μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
-  simp only [measureReal_def]
+  simp only [carleson_measureReal_def]
   rw [← ENNReal.toReal_add, measure_inter_add_diff₀ s ht]
-  · exact measure_ne_top_of_subset inter_subset_left h
-  · exact measure_ne_top_of_subset diff_subset h
-
-theorem measureReal_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ)
+  · exact carleson_measure_ne_top_of_subset inter_subset_left h
+  · exact carleson_measure_ne_top_of_subset diff_subset h
+
+theorem carleson_measureReal_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
   have : μ (s ∪ t) ≠ ∞ :=
     ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩ )).ne
-  rw [← measureReal_inter_add_diff₀ (s ∪ t) ht this, Set.union_inter_cancel_right, union_diff_right,
-    ← measureReal_inter_add_diff₀ s ht h₁]
+  rw [← carleson_measureReal_inter_add_diff₀ (s ∪ t) ht this, Set.union_inter_cancel_right, union_diff_right,
+    ← carleson_measureReal_inter_add_diff₀ s ht h₁]
   ac_rfl
 
-theorem measureReal_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α)
+theorem carleson_measureReal_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
-  rw [union_comm, inter_comm, measureReal_union_add_inter₀ t hs h₂ h₁, add_comm]
-
-theorem measureReal_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
+  rw [union_comm, inter_comm, carleson_measureReal_union_add_inter₀ t hs h₂ h₁, add_comm]
+
+theorem carleson_measureReal_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real (s ∪ t) = μ.real s + μ.real t := by
   simp only [Measure.real]
   rw [measure_union₀ ht hd, ENNReal.toReal_add h₁ h₂]
 
-theorem measureReal_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
+theorem carleson_measureReal_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real (s ∪ t) = μ.real s + μ.real t := by
-  rw [union_comm, measureReal_union₀ hs (AEDisjoint.symm hd) h₂ h₁, add_comm]
-
-theorem measureReal_add_measureReal_compl₀ [IsFiniteMeasure μ] {s : Set α}
+  rw [union_comm, carleson_measureReal_union₀ hs (AEDisjoint.symm hd) h₂ h₁, add_comm]
+
+theorem carleson_measureReal_add_measureReal_compl₀ [IsFiniteMeasure μ] {s : Set α}
     (hs : NullMeasurableSet s μ) :
     μ.real s + μ.real sᶜ = μ.real univ := by
-  rw [← measureReal_union₀' hs aedisjoint_compl_right, union_compl_self]
-
-theorem measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
+  rw [← carleson_measureReal_union₀' hs aedisjoint_compl_right, union_compl_self]
+
+theorem carleson_measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
     (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
     μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ :=
-  measureReal_union₀ h.nullMeasurableSet hd.aedisjoint h₁ h₂
-
-theorem measureReal_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
+  carleson_measureReal_union₀ h.nullMeasurableSet hd.aedisjoint h₁ h₂
+
+theorem carleson_measureReal_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
     (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
     μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ :=
-  measureReal_union₀' h.nullMeasurableSet hd.aedisjoint h₁ h₂
-
-theorem measureReal_inter_add_diff (s : Set α) (ht : MeasurableSet t)
+  carleson_measureReal_union₀' h.nullMeasurableSet hd.aedisjoint h₁ h₂
+
+theorem carleson_measureReal_inter_add_diff (s : Set α) (ht : MeasurableSet t)
     (h : μ s ≠ ∞ := by finiteness) :
     μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
   simp only [Measure.real]
   rw [← ENNReal.toReal_add, measure_inter_add_diff _ ht]
-  · exact measure_ne_top_of_subset inter_subset_left h
-  · exact measure_ne_top_of_subset diff_subset h
-
-theorem measureReal_diff_add_inter (s : Set α) (ht : MeasurableSet t)
+  · exact carleson_measure_ne_top_of_subset inter_subset_left h
+  · exact carleson_measure_ne_top_of_subset diff_subset h
+
+theorem carleson_measureReal_diff_add_inter (s : Set α) (ht : MeasurableSet t)
     (h : μ s ≠ ∞ := by finiteness) :
     μ.real (s \ t) + μ.real (s ∩ t) = μ.real s :=
-  (add_comm _ _).trans (measureReal_inter_add_diff s ht h)
-
-theorem measureReal_union_add_inter (s : Set α) (ht : MeasurableSet t)
+  (add_comm _ _).trans (carleson_measureReal_inter_add_diff s ht h)
+
+theorem carleson_measureReal_union_add_inter (s : Set α) (ht : MeasurableSet t)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t :=
-  measureReal_union_add_inter₀ s ht.nullMeasurableSet h₁ h₂
-
-theorem measureReal_union_add_inter' (hs : MeasurableSet s) (t : Set α)
+  carleson_measureReal_union_add_inter₀ s ht.nullMeasurableSet h₁ h₂
+
+theorem carleson_measureReal_union_add_inter' (hs : MeasurableSet s) (t : Set α)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t :=
-  measureReal_union_add_inter₀' hs.nullMeasurableSet t h₁ h₂
-
-lemma measureReal_symmDiff_eq (hs : MeasurableSet s) (ht : MeasurableSet t)
+  carleson_measureReal_union_add_inter₀' hs.nullMeasurableSet t h₁ h₂
+
+lemma carleson_measureReal_symmDiff_eq (hs : MeasurableSet s) (ht : MeasurableSet t)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real (s ∆ t) = μ.real (s \ t) + μ.real (t \ s) := by
   simp only [Measure.real]
   rw [← ENNReal.toReal_add, measure_symmDiff_eq hs.nullMeasurableSet ht.nullMeasurableSet]
-  · exact measure_ne_top_of_subset diff_subset h₁
-  · exact measure_ne_top_of_subset diff_subset h₂
-
-lemma measureReal_symmDiff_le (s t u : Set α)
+  · exact carleson_measure_ne_top_of_subset diff_subset h₁
+  · exact carleson_measure_ne_top_of_subset diff_subset h₂
+
+lemma carleson_measureReal_symmDiff_le (s t u : Set α)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real (s ∆ u) ≤ μ.real (s ∆ t) + μ.real (t ∆ u) := by
   rcases eq_top_or_lt_top (μ u) with hu|hu
-  · simp only [measureReal_def, measure_symmDiff_eq_top h₁ hu, ENNReal.top_toReal]
+  · simp only [carleson_measureReal_def, carleson_measure_symmDiff_eq_top h₁ hu, ENNReal.toReal_top]
     exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
-  · exact le_trans (measureReal_mono (symmDiff_triangle s t u) (measure_union_ne_top
+  · exact le_trans (carleson_measureReal_mono (symmDiff_triangle s t u) (measure_union_ne_top
       (measure_symmDiff_ne_top h₁ h₂) (measure_symmDiff_ne_top h₂ hu.ne)))
-        (measureReal_union_le (s ∆ t) (t ∆ u))
-
-theorem measureReal_add_measureReal_compl [IsFiniteMeasure μ] (h : MeasurableSet s) :
+        (carleson_measureReal_union_le (s ∆ t) (t ∆ u))
+
+theorem carleson_measureReal_add_measureReal_compl [IsFiniteMeasure μ] (h : MeasurableSet s) :
     μ.real s + μ.real sᶜ = μ.real univ :=
-  measureReal_add_measureReal_compl₀ h.nullMeasurableSet
-
-theorem measureReal_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
+  carleson_measureReal_add_measureReal_compl₀ h.nullMeasurableSet
+
+theorem carleson_measureReal_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
     (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ)
     (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
-    μ.real (⋃ b ∈ s, f b) = ∑ p in s, μ.real (f p) := by
-  simp only [measureReal_def, measure_biUnion_finset₀ hd hm, ENNReal.toReal_sum h]
-
-theorem measureReal_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
+    μ.real (⋃ b ∈ s, f b) = ∑ p ∈ s, μ.real (f p) := by
+  simp only [carleson_measureReal_def, measure_biUnion_finset₀ hd hm, ENNReal.toReal_sum h]
+
+theorem carleson_measureReal_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
     (hm : ∀ b ∈ s, MeasurableSet (f b)) (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
-    μ.real (⋃ b ∈ s, f b) = ∑ p in s, μ.real (f p) :=
-  measureReal_biUnion_finset₀ hd.aedisjoint (fun b hb ↦ (hm b hb).nullMeasurableSet) h
+    μ.real (⋃ b ∈ s, f b) = ∑ p ∈ s, μ.real (f p) :=
+  carleson_measureReal_biUnion_finset₀ hd.aedisjoint (fun b hb ↦ (hm b hb).nullMeasurableSet) h
 
 /-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
 of the fibers `f ⁻¹' {y}`. -/
-theorem sum_measureReal_preimage_singleton (s : Finset β) {f : α → β}
+theorem carleson_sum_measureReal_preimage_singleton (s : Finset β) {f : α → β}
     (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) (h : ∀ a ∈ s, μ (f ⁻¹' {a}) ≠ ∞ := by finiteness) :
-    (∑ b in s, μ.real (f ⁻¹' {b})) = μ.real (f ⁻¹' ↑s) := by
-  simp only [measureReal_def, ← sum_measure_preimage_singleton s hf, ENNReal.toReal_sum h]
+    (∑ b ∈ s, μ.real (f ⁻¹' {b})) = μ.real (f ⁻¹' ↑s) := by
+  simp only [carleson_measureReal_def, ← sum_measure_preimage_singleton s hf, ENNReal.toReal_sum h]
 
 /-- If `s` is a `Finset`, then the sums of the real measures of the singletons in the set is the
 real measure of the set. -/
-@[simp] theorem Finset.sum_realMeasure_singleton [MeasurableSingletonClass α] [IsFiniteMeasure μ]
+@[simp] theorem Finset.carleson_sum_realMeasure_singleton [MeasurableSingletonClass α] [IsFiniteMeasure μ]
     (s : Finset α) :
-    (∑ b in s, μ.real {b}) = μ.real s :=
-  Finset.sum_toReal_measure_singleton ..
-
-theorem measureReal_diff_null' (h : μ.real (s₁ ∩ s₂) = 0) (h' : μ s₁ ≠ ∞ := by finiteness) :
+    (∑ b ∈ s, μ.real {b}) = μ.real s :=
+  Finset.carleson_sum_toReal_measure_singleton ..
+
+theorem carleson_measureReal_diff_null' (h : μ.real (s₁ ∩ s₂) = 0) (h' : μ s₁ ≠ ∞ := by finiteness) :
     μ.real (s₁ \ s₂) = μ.real s₁ := by
-  simp only [measureReal_def]
+  simp only [carleson_measureReal_def]
   rw [measure_diff_null']
-  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset inter_subset_left h')).1 h
-
-theorem measureReal_diff_null (h : μ.real s₂ = 0) (h' : μ s₂ ≠ ∞ := by finiteness) :
+  exact (carleson_measureReal_eq_zero_iff (carleson_measure_ne_top_of_subset inter_subset_left h')).1 h
+
+theorem carleson_measureReal_diff_null (h : μ.real s₂ = 0) (h' : μ s₂ ≠ ∞ := by finiteness) :
     μ.real (s₁ \ s₂) = μ.real s₁ := by
   rcases eq_top_or_lt_top (μ s₁) with H|H
-  · simp [measureReal_def, H, measure_diff_eq_top H h']
-  · exact measureReal_diff_null' (measureReal_mono_null inter_subset_right h h') H.ne
-
-theorem measureReal_add_diff (hs : MeasurableSet s) (t : Set α)
+  · simp [carleson_measureReal_def, H, carleson_measure_diff_eq_top H h']
+  · exact carleson_measureReal_diff_null' (carleson_measureReal_mono_null inter_subset_right h h') H.ne
+
+theorem carleson_measureReal_add_diff (hs : MeasurableSet s) (t : Set α)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real s + μ.real (t \ s) = μ.real (s ∪ t) := by
-  rw [← measureReal_union' (@disjoint_sdiff_right _ s t) hs h₁
-    (measure_ne_top_of_subset diff_subset h₂), union_diff_self]
-
-theorem measureReal_diff' (s : Set α) (hm : MeasurableSet t)
+  rw [← carleson_measureReal_union' (@disjoint_sdiff_right _ s t) hs h₁
+    (carleson_measure_ne_top_of_subset diff_subset h₂), union_diff_self]
+
+theorem carleson_measureReal_diff' (s : Set α) (hm : MeasurableSet t)
     (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
     μ.real (s \ t) = μ.real (s ∪ t) - μ.real t := by
-  rw [union_comm, ← measureReal_add_diff hm s h₂ h₁]
+  rw [union_comm, ← carleson_measureReal_add_diff hm s h₂ h₁]
   ring
 
-theorem measureReal_diff (h : s₂ ⊆ s₁) (h₂ : MeasurableSet s₂)
+theorem carleson_measureReal_diff (h : s₂ ⊆ s₁) (h₂ : MeasurableSet s₂)
     (h₁ : μ s₁ ≠ ∞ := by finiteness) :
     μ.real (s₁ \ s₂) = μ.real s₁ - μ.real s₂ := by
-  rw [measureReal_diff' _ h₂ h₁ (measure_ne_top_of_subset h h₁), union_eq_self_of_subset_right h]
-
-theorem le_measureReal_diff (h : μ s₂ ≠ ∞ := by finiteness) :
+  rw [carleson_measureReal_diff' _ h₂ h₁ (carleson_measure_ne_top_of_subset h h₁), union_eq_self_of_subset_right h]
+
+theorem carleson_le_measureReal_diff (h : μ s₂ ≠ ∞ := by finiteness) :
     μ.real s₁ - μ.real s₂ ≤ μ.real (s₁ \ s₂) := by
   simp only [tsub_le_iff_left]
   calc
-    μ.real s₁ ≤ μ.real (s₂ ∪ s₁) := measureReal_le_measureReal_union_right h
+    μ.real s₁ ≤ μ.real (s₂ ∪ s₁) := carleson_measureReal_le_measureReal_union_right h
     _ = μ.real (s₂ ∪ s₁ \ s₂) := congr_arg μ.real union_diff_self.symm
-    _ ≤ μ.real s₂ + μ.real (s₁ \ s₂) := measureReal_union_le _ _
-
-theorem measureReal_diff_lt_of_lt_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
+    _ ≤ μ.real s₂ + μ.real (s₁ \ s₂) := carleson_measureReal_union_le _ _
+
+theorem carleson_measureReal_diff_lt_of_lt_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
     (h : μ.real t < μ.real s + ε) (ht' : μ t ≠ ∞ := by finiteness) :
     μ.real (t \ s) < ε := by
-  rw [measureReal_diff hst hs ht']; linarith
-
-theorem measureReal_diff_le_iff_le_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
+  rw [carleson_measureReal_diff hst hs ht']; linarith
+
+theorem carleson_measureReal_diff_le_iff_le_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
     (ht' : μ t ≠ ∞ := by finiteness) :
     μ.real (t \ s) ≤ ε ↔ μ.real t ≤ μ.real s + ε := by
-  rw [measureReal_diff hst hs ht', tsub_le_iff_left]
-
-theorem measureReal_eq_measureReal_of_null_diff {s t : Set α} (hst : s ⊆ t)
+  rw [carleson_measureReal_diff hst hs ht', tsub_le_iff_left]
+
+theorem carleson_measureReal_eq_measureReal_of_null_diff {s t : Set α} (hst : s ⊆ t)
     (h_nulldiff : μ.real (t \ s) = 0) (h : μ (t \ s) ≠ ∞ := by finiteness) :
     μ.real s = μ.real t := by
-  rw [measureReal_eq_zero_iff h] at h_nulldiff
-  simp [measureReal_def, measure_eq_measure_of_null_diff hst h_nulldiff]
-
-theorem measureReal_eq_measureReal_of_between_null_diff {s₁ s₂ s₃ : Set α}
+  rw [carleson_measureReal_eq_zero_iff h] at h_nulldiff
+  simp [carleson_measureReal_def, measure_eq_measure_of_null_diff hst h_nulldiff]
+
+theorem carleson_measureReal_eq_measureReal_of_between_null_diff {s₁ s₂ s₃ : Set α}
     (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
     (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
     μ.real s₁ = μ.real s₂ ∧ μ.real s₂ = μ.real s₃ := by
   have A : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ :=
-    measure_eq_measure_of_between_null_diff h12 h23 ((measureReal_eq_zero_iff h').1 h_nulldiff)
-  simp [measureReal_def, A.1, A.2]
-
-theorem measureReal_eq_measureReal_smaller_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
+    measure_eq_measure_of_between_null_diff h12 h23 ((carleson_measureReal_eq_zero_iff h').1 h_nulldiff)
+  simp [carleson_measureReal_def, A.1, A.2]
+
+theorem carleson_measureReal_eq_measureReal_smaller_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
     (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
     (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
     μ.real s₁ = μ.real s₂ :=
-  (measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').1
-
-theorem measureReal_eq_measureReal_larger_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
+  (carleson_measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').1
+
+theorem carleson_measureReal_eq_measureReal_larger_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
     (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
     μ.real s₂ = μ.real s₃ :=
-  (measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').2
-
-theorem measureReal_compl [IsFiniteMeasure μ] (h₁ : MeasurableSet s) :
+  (carleson_measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').2
+
+theorem carleson_measureReal_compl [IsFiniteMeasure μ] (h₁ : MeasurableSet s) :
     μ.real sᶜ = μ.real univ - μ.real s := by
   rw [compl_eq_univ_diff]
-  exact measureReal_diff (subset_univ s) h₁
-
-theorem measureReal_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂)
+  exact carleson_measureReal_diff (subset_univ s) h₁
+
+theorem carleson_measureReal_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂)
     (hsμ : μ.real s₂ ≤ μ.real s₁) (ht : t₁ ⊆ t₂) (htμ : μ.real t₂ ≤ μ.real t₁)
     (h₁ : μ s₂ ≠ ∞ := by finiteness) (h₂ : μ t₂ ≠ ∞ := by finiteness) :
     μ.real (s₁ ∪ t₁) = μ.real (s₂ ∪ t₂) := by
-  simp only [measureReal_def]
+  simp only [carleson_measureReal_def]
   rw [measure_union_congr_of_subset hs _ ht]
-  · exact (ENNReal.toReal_le_toReal h₂ (measure_ne_top_of_subset ht h₂)).1 htμ
-  · exact (ENNReal.toReal_le_toReal h₁ (measure_ne_top_of_subset hs h₁)).1 hsμ
-
-theorem sum_measureReal_le_measureReal_univ [IsFiniteMeasure μ] {s : Finset ι} {t : ι → Set α}
+  · exact (ENNReal.toReal_le_toReal h₂ (carleson_measure_ne_top_of_subset ht h₂)).1 htμ
+  · exact (ENNReal.toReal_le_toReal h₁ (carleson_measure_ne_top_of_subset hs h₁)).1 hsμ
+
+theorem carleson_sum_measureReal_le_measureReal_univ [IsFiniteMeasure μ] {s : Finset ι} {t : ι → Set α}
     (h : ∀ i ∈ s, MeasurableSet (t i)) (H : Set.PairwiseDisjoint (↑s) t) :
-    (∑ i in s, μ.real (t i)) ≤ μ.real (univ : Set α) := by
-  simp only [measureReal_def]
+    (∑ i ∈ s, μ.real (t i)) ≤ μ.real (univ : Set α) := by
+  simp only [carleson_measureReal_def]
   rw [← ENNReal.toReal_sum (fun i hi ↦ measure_ne_top _ _)]
   apply ENNReal.toReal_mono (measure_ne_top _ _)
   exact sum_measure_le_measure_univ (fun i mi ↦ (h i mi).nullMeasurableSet) H.aedisjoint
 
 /-- Pigeonhole principle for measure spaces: if `s` is a `Finset` and
-`∑ i in s, μ.real (t i) > μ.real univ`, then one of the intersections `t i ∩ t j` is not empty. -/
-theorem exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal
+`∑ i ∈ s, μ.real (t i) > μ.real univ`, then one of the intersections `t i ∩ t j` is not empty. -/
+theorem carleson_exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal
     {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
     {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, MeasurableSet (t i))
-    (H : μ.real (univ : Set α) < ∑ i in s, μ.real (t i)) :
+    (H : μ.real (univ : Set α) < ∑ i ∈ s, μ.real (t i)) :
     ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
   apply exists_nonempty_inter_of_measure_univ_lt_sum_measure μ
     (fun i mi ↦ (h i mi).nullMeasurableSet)
   apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) _).1
-  · convert H
-    rw [ENNReal.toReal_sum (fun i hi ↦ measure_ne_top _ _)]
-    rfl
+  · simpa only [carleson_measureReal_def, ENNReal.toReal_sum (fun i hi ↦ measure_ne_top _ _)] using H
   · exact (ENNReal.sum_lt_top.mpr (fun i hi ↦ measure_lt_top ..)).ne
 
 /-- If two sets `s` and `t` are included in a set `u` of finite measure,
 and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
 Version assuming that `t` is measurable. -/
-theorem nonempty_inter_of_measureReal_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
+theorem carleson_nonempty_inter_of_measureReal_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
     (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
     (hu : μ u ≠ ∞ := by finiteness) :
     (s ∩ t).Nonempty := by
   apply nonempty_inter_of_measure_lt_add μ ht h's h't ?_
   apply (ENNReal.toReal_lt_toReal hu _).1
-  · rw [ENNReal.toReal_add (measure_ne_top_of_subset h's hu) (measure_ne_top_of_subset h't hu)]
+  · rw [ENNReal.toReal_add (carleson_measure_ne_top_of_subset h's hu) (carleson_measure_ne_top_of_subset h't hu)]
     exact h
-  · exact ENNReal.add_ne_top.2 ⟨measure_ne_top_of_subset h's hu, measure_ne_top_of_subset h't hu⟩
+  · exact ENNReal.add_ne_top.2 ⟨carleson_measure_ne_top_of_subset h's hu, carleson_measure_ne_top_of_subset h't hu⟩
 
 /-- If two sets `s` and `t` are included in a set `u` of finite measure,
 and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
 Version assuming that `s` is measurable. -/
-theorem nonempty_inter_of_measureReal_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
+theorem carleson_nonempty_inter_of_measureReal_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
     (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
     (hu : μ u ≠ ∞ := by finiteness) :
     (s ∩ t).Nonempty := by
   rw [add_comm] at h
   rw [inter_comm]
-  exact nonempty_inter_of_measureReal_lt_add μ hs h't h's h hu
-
-theorem measureReal_prod_prod [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SigmaFinite ν]
+  exact carleson_nonempty_inter_of_measureReal_lt_add μ hs h't h's h hu
+
+theorem carleson_measureReal_prod_prod [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SigmaFinite ν]
     (s : Set α) (t : Set β) : (μ.prod ν).real (s ×ˢ t) = μ.real s * ν.real t := by
-  simp only [measureReal_def, prod_prod, ENNReal.toReal_mul]
-
-theorem ext_iff_measureReal_singleton {S} [Fintype S] [MeasurableSpace S]
+  simp only [carleson_measureReal_def, prod_prod, ENNReal.toReal_mul]
+
+theorem carleson_ext_iff_measureReal_singleton {S} [Fintype S] [MeasurableSpace S]
     [MeasurableSingletonClass S]
     {μ1 μ2 : Measure S} [IsFiniteMeasure μ1] [IsFiniteMeasure μ2] :
     μ1 = μ2 ↔ ∀ x, μ1.real {x} = μ2.real {x} := by
   rw [Measure.ext_iff_singleton]
   congr! with x
-  rw [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff]
+  rw [carleson_measureReal_def, carleson_measureReal_def, ENNReal.toReal_eq_toReal_iff]
   simp [measure_ne_top]
 
 end MeasureTheory
@@ -468,9 +467,10 @@
 
 /-- Extension for the `positivity` tactic: applications of `μ.real` are nonnegative. -/
 @[positivity MeasureTheory.Measure.real _ _]
-def evalMeasureReal : PositivityExt where eval {_ _} _zα _pα e := do
+meta def carlesonEvalMeasureReal : PositivityExt where eval {_ _} _zα pα? e :=
+  match pα? with | none => pure .none | some _ => do
   let .app (.app _ a) b ← whnfR e | throwError "not measureReal"
-  let p ← mkAppOptM ``MeasureTheory.measureReal_nonneg #[none, none, a, b]
+  let p ← mkAppOptM ``MeasureTheory.carleson_measureReal_nonneg #[none, none, a, b]
   pure (.nonnegative p)
 
 end Mathlib.Meta.Positivity
```

## Carleson/ToMathlib/Misc.lean

```diff
--- upstream/Carleson/ToMathlib/Misc.lean
+++ lean-4.34.1/Carleson/ToMathlib/Misc.lean
@@ -1,7 +1,7 @@
 import Mathlib.Analysis.Convex.PartitionOfUnity
 import Mathlib.Analysis.Calculus.ContDiff.Basic
 import Mathlib.MeasureTheory.Integral.Average
-import Mathlib.MeasureTheory.Integral.Bochner
+import Mathlib.MeasureTheory.Integral.Bochner.Basic
 import Mathlib.MeasureTheory.Measure.Haar.OfBasis
 import Mathlib.Topology.MetricSpace.Holder
 import Mathlib.Data.Set.Card
@@ -19,39 +19,7 @@
 section ENNReal
 
 lemma tsum_one_eq' {α : Type*} (s : Set α) : ∑' (_:s), (1 : ℝ≥0∞) = s.encard := by
-  if hfin : s.Finite then
-    have hfin' : Finite s := hfin
-    rw [tsum_def]
-    simp only [ENNReal.summable, ↓reduceDIte]
-    have hsup: support (fun (_ : s) ↦ (1 : ℝ≥0∞)) = Set.univ := by
-      ext i
-      simp only [mem_support, ne_eq, one_ne_zero, not_false_eq_true, mem_univ]
-    have hsupfin: (Set.univ : Set s).Finite := finite_univ
-    rw [← hsup] at hsupfin
-    rw [if_pos hsupfin]
-    rw [hfin.encard_eq_coe_toFinset_card]
-    simp only [ENat.toENNReal_coe]
-    rw [Finset.card_eq_sum_ones]
-    rw [finsum_eq_sum (fun (_ : s) ↦ (1 :ℝ≥0∞)) hsupfin]
-    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul, Nat.cast_inj]
-    apply Finset.card_bij (fun a _ => a.val)
-    · intro a
-      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
-        Subtype.coe_prop, imp_self]
-    · intro a _ a' _ heq
-      ext
-      exact heq
-    · intro a ha
-      use ⟨a,by
-        simp only [Finite.mem_toFinset] at ha
-        exact ha⟩
-      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
-        exists_const]
-  else
-  have : Infinite s := infinite_coe_iff.mpr hfin
-  rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)]
-  rw [Set.encard_eq_top_iff.mpr hfin]
-  simp only [ENat.toENNReal_top]
+  exact ENNReal.tsum_set_one s
 
 lemma ENNReal.tsum_const_eq' {α : Type*} (s : Set α) (c : ℝ≥0∞) :
     ∑' (_:s), (c : ℝ≥0∞) = s.encard * c := by
@@ -76,8 +44,8 @@
   rw [← coe_inv this, coe_inj, Real.toNNReal_inv, one_div]
 
 lemma ENNReal.sum_geometric_two_pow_neg_one : ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-n : ℤ) = 2 := by
-  conv_lhs => enter [1, n]; rw [← one_mul (n : ℤ), ← neg_mul, ← Nat.cast_one]
-  rw [ENNReal.sum_geometric_two_pow_toNNReal zero_lt_one]; norm_num
+  convert ENNReal.sum_geometric_two_pow_toNNReal zero_lt_one using 1 <;> norm_num
+
 
 lemma ENNReal.sum_geometric_two_pow_neg_two :
     ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-2 * n : ℤ) = ((4 : ℝ) / 3).toNNReal := by
@@ -99,7 +67,7 @@
 end ENNReal
 
 section Indicator
-attribute [gcongr] Set.indicator_le_indicator mulIndicator_le_mulIndicator_of_subset
+attribute [gcongr only] Set.indicator_le_indicator mulIndicator_le_mulIndicator_of_subset
 end Indicator
 
 
@@ -111,7 +79,7 @@
 lemma lintegral_Ioc_partition {a b : ℕ} {c : ℝ} {f : ℝ → ℝ≥0∞} (hc : 0 ≤ c) :
     ∫⁻ t in Ioc (a * c) (b * c), f t =
     ∑ l ∈ Finset.Ico a b, ∫⁻ t in Ioc (l * c) ((l + 1 : ℕ) * c), f t := by
-  rcases lt_or_le b a with h | h
+  rcases lt_or_ge b a with h | h
   · rw [Finset.Ico_eq_empty (by omega), Ioc_eq_empty (by rw [not_lt]; gcongr),
       setLIntegral_empty, Finset.sum_empty]
   induction b, h using Nat.le_induction with
@@ -120,8 +88,8 @@
   | succ b h ih =>
     have li : a * c ≤ b * c := by gcongr
     rw [← Ioc_union_Ioc_eq_Ioc li (by gcongr; omega),
-      lintegral_union measurableSet_Ioc Ioc_disjoint_Ioc_same,
-      Nat.Ico_succ_right_eq_insert_Ico h, Finset.sum_insert Finset.right_not_mem_Ico,
+      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
+      Nat.Ico_succ_right_eq_insert_Ico h, Finset.sum_insert (by simp),
       add_comm (lintegral ..), ih]
 
 /-! ## Averaging -/
@@ -152,13 +120,13 @@
 lemma setLaverage_add_left' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
     {s : Set α} {f g : α → ENNReal} (hf : AEMeasurable f μ) :
     ⨍⁻ x in s, (f x + g x) ∂μ = ⨍⁻ x in s, f x ∂μ + ⨍⁻ x in s, g x ∂μ := by
-  simp_rw [setLaverage_eq, ENNReal.div_add_div_same, lintegral_add_left' hf.restrict]
+  simp_rw [setLAverage_eq, ENNReal.div_add_div_same, lintegral_add_left' hf.restrict]
 
 -- Named for consistency with `setLintegral_mono'`
 lemma setLaverage_mono' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
     {s : Set α} (hs : MeasurableSet s) {f g : α → ENNReal} (h : ∀ x ∈ s, f x ≤ g x) :
     ⨍⁻ x in s, f x ∂μ ≤ ⨍⁻ x in s, g x ∂μ := by
-  simp_rw [setLaverage_eq]
+  simp_rw [setLAverage_eq]
   exact ENNReal.div_le_div_right (setLIntegral_mono' hs h) (μ s)
 
 end MeasureTheory
@@ -168,7 +136,7 @@
   {F : Type*} [NormedAddCommGroup F]
 
 attribute [fun_prop] Continuous.comp_aestronglyMeasurable
-  AEStronglyMeasurable.mul AEStronglyMeasurable.prod_mk
+  AEStronglyMeasurable.mul AEStronglyMeasurable.prodMk
 attribute [gcongr] Measure.AbsolutelyContinuous.prod -- todo: also add one-sided versions for gcongr
 
 
@@ -177,17 +145,17 @@
   refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
   exact ENNReal.measurable_toReal.comp_aemeasurable hu.aemeasurable
 
-lemma laverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
+lemma carleson_laverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
     ⨍⁻ a, f a ∂μ ≤ ⨍⁻ a, g a ∂μ := by
   exact lintegral_mono_ae <| h.filter_mono <| Measure.ae_mono' Measure.smul_absolutelyContinuous
 
-@[gcongr]
-lemma setLAverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
+@[gcongr only]
+lemma carleson_setLAverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
     ⨍⁻ a in s, f a ∂μ ≤ ⨍⁻ a in s, g a ∂μ := by
-  refine laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self
+  refine carleson_laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self
 
 lemma setLaverage_const_le {c : ℝ≥0∞} : ⨍⁻ _x in s, c ∂μ ≤ c := by
-  simp_rw [setLaverage_eq, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
+  simp_rw [setLAverage_eq, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
     univ_inter, div_eq_mul_inv, mul_assoc]
   conv_rhs => rw [← mul_one c]
   gcongr
@@ -201,7 +169,7 @@
   ext; simp [ENNReal.toReal]
 
 theorem restrict_absolutelyContinuous : μ.restrict s ≪ μ :=
-  fun s hs ↦ Measure.restrict_le_self s |>.trans hs.le |>.antisymm <| zero_le _
+  fun s hs ↦ Measure.restrict_le_self s |>.trans hs.le |>.antisymm <| (by positivity)
 
 end MeasureTheory
 
@@ -312,7 +280,7 @@
 end Set.Finite
 
 lemma Real.self_lt_two_rpow (x : ℝ) : x < 2 ^ x := by
-  rcases lt_or_le x 0 with h | h
+  rcases lt_or_ge x 0 with h | h
   · exact h.trans (rpow_pos_of_pos zero_lt_two x)
   · calc
       _ < (⌊x⌋₊.succ : ℝ) := Nat.lt_succ_floor x
@@ -385,7 +353,7 @@
 -- must be in mathlib but can't find it
 theorem indicator_const {c : ℝ} {s: Set X}
     (hs: MeasurableSet s) (h2s : volume s < ⊤) : Integrable (s.indicator (fun _ ↦ c)) :=
-  (integrable_indicator_iff hs).mpr <| integrableOn_const.mpr <| Or.inr h2s
+  (integrable_indicator_iff hs).mpr <| integrableOn_const h2s.ne
 
 end Integrable
 
@@ -438,7 +406,7 @@
     · simp [hi, μ₀]
 
 -- Analogous to `MeasureTheory.integral_smul_const` in Mathlib
-theorem average_smul_const {X : Type*} {E : Type*} [MeasurableSpace X]
+theorem carleson_average_smul_const {X : Type*} {E : Type*} [MeasurableSpace X]
     {μ : MeasureTheory.Measure X} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*}
     [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E] (f : X → 𝕜) (c : E) :
     ⨍ (x : X), f x • c ∂μ = (⨍ (x : X), f x ∂μ) • c :=
```

## Carleson/CoverByBalls.lean

```diff
--- upstream/Carleson/CoverByBalls.lean
+++ lean-4.34.1/Carleson/CoverByBalls.lean
@@ -44,7 +44,7 @@
   refine ⟨fun ⟨_, _, hs⟩ ↦ ?_, fun hs ↦ ?_⟩
   · simpa using hs
   · have h22 : s ⊆ ⋃ x ∈ (∅ : Finset X), ball x 0 := by
-      simp only [not_mem_empty, ball_zero, Set.iUnion_of_empty, Set.iUnion_empty]
+      simp only [Finset.notMem_empty, ball_zero, Set.iUnion_of_empty, Set.iUnion_empty]
       exact Set.subset_empty_iff.mpr hs
     use ∅, tsub_add_cancel_iff_le.mp rfl, h22
 
@@ -87,7 +87,7 @@
 lemma BallsCoverBalls.pow_mul {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls X (a * r) r n) :
     BallsCoverBalls X (a^k * r) r (n^k) := by
   induction k with
-  | zero => simpa using fun x ↦ BallCoversSelf x r
+  | zero => simpa only [pow_zero, one_mul, BallsCoverBalls] using fun x ↦ BallCoversSelf x r
   | succ m h2 =>
     specialize h (r * a^m)
     rw [← mul_assoc, mul_comm, ← mul_assoc] at h
```

## Carleson/DoublingMeasure.lean

```diff
--- upstream/Carleson/DoublingMeasure.lean
+++ lean-4.34.1/Carleson/DoublingMeasure.lean
@@ -1,3 +1,4 @@
+import Mathlib.Analysis.SpecialFunctions.Log.Base
 import Carleson.CoverByBalls
 import Mathlib.Data.Real.StarOrdered
 import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
@@ -100,18 +101,18 @@
       (measure_real_ball_two_le_same _ _) (zero_le_coe)
     _ = A ^ 2 * μ.real (ball x r) := by ring_nf
 
-lemma measure_ball_ne_top (x : X) (r : ℝ) : μ (ball x r) ≠ ∞ := measure_ball_lt_top.ne
+lemma carleson_measure_ball_ne_top (x : X) (r : ℝ) : μ (ball x r) ≠ ∞ := measure_ball_lt_top.ne
 
 lemma measure_ball_four_le_same' (x : X) (r : ℝ) :
     μ (ball x (4 * r)) ≤ A ^ 2 * μ (ball x r) := by
   have hfactor : (A ^ 2 : ℝ≥0∞) ≠ ⊤ := ne_of_beq_false rfl
-  rw [← ENNReal.ofReal_toReal (measure_ball_ne_top x (4 * r)),
-    ← ENNReal.ofReal_toReal (measure_ball_ne_top x r), ← ENNReal.ofReal_toReal hfactor,
+  rw [← ENNReal.ofReal_toReal (carleson_measure_ball_ne_top x (4 * r)),
+    ← ENNReal.ofReal_toReal (carleson_measure_ball_ne_top x r), ← ENNReal.ofReal_toReal hfactor,
     ← ENNReal.ofReal_mul]
   · exact ENNReal.ofReal_le_ofReal <| measure_ball_four_le_same x r
   · simp
 
-attribute [aesop (rule_sets := [finiteness]) safe apply] measure_ball_ne_top
+attribute [aesop (rule_sets := [finiteness]) safe apply] carleson_measure_ball_ne_top
 
 lemma measure_ball_le_pow_two {x : X} {r : ℝ} {n : ℕ} :
     μ.real (ball x (2 ^ n * r)) ≤ A ^ n * μ.real (ball x r) := by
@@ -130,8 +131,8 @@
 
 lemma measure_ball_le_pow_two' {x : X} {r : ℝ} {n : ℕ} :
     μ (ball x (2 ^ n * r)) ≤ A ^ n * μ (ball x r) := by
-  have hleft : μ (ball x (2 ^ n * r)) ≠ ⊤ := measure_ball_ne_top x (2 ^ n * r)
-  have hright : μ (ball x r) ≠ ⊤ := measure_ball_ne_top x r
+  have hleft : μ (ball x (2 ^ n * r)) ≠ ⊤ := carleson_measure_ball_ne_top x (2 ^ n * r)
+  have hright : μ (ball x r) ≠ ⊤ := carleson_measure_ball_ne_top x r
   have hfactor : (A ^n : ℝ≥0∞) ≠ ⊤ := Ne.symm (ne_of_beq_false rfl)
   rw [← ENNReal.ofReal_toReal hleft,← ENNReal.ofReal_toReal hright,← ENNReal.ofReal_toReal hfactor,
     ← ENNReal.ofReal_mul]
@@ -181,8 +182,8 @@
 lemma measure_ball_le_same (x : X) {r s r': ℝ} (hsp : 0 < s) (hs : r' ≤ s * r) :
     μ.real (ball x r') ≤ As A s * μ.real (ball x r) := by
   have hz := measure_ball_le_same' (μ := μ) x hsp hs
-  have hbr': μ (ball x r') ≠ ⊤ := measure_ball_ne_top x r'
-  have hbr: μ (ball x r) ≠ ⊤ := measure_ball_ne_top x r
+  have hbr': μ (ball x r') ≠ ⊤ := carleson_measure_ball_ne_top x r'
+  have hbr: μ (ball x r) ≠ ⊤ := carleson_measure_ball_ne_top x r
   have hAs : (As A s: ℝ≥0∞) ≠ ⊤ := coe_ne_top
   rw [← ENNReal.ofReal_toReal hbr,← ENNReal.ofReal_toReal hbr',
     ← ENNReal.ofReal_toReal hAs, ← ENNReal.ofReal_mul] at hz
@@ -202,9 +203,9 @@
 
 lemma measureNNReal_ball_le_of_dist_le' {x x' : X} {r r' s : ℝ} (hs : 0 < s)
     (h : dist x x' + r' ≤ s * r) :
-    μ.nnreal (ball x' r') ≤ As A s * μ.nnreal (ball x r) := by
-  simp only [Measure.nnreal,← ENNReal.coe_le_coe, coe_mul, ENNReal.coe_toNNReal
-    (measure_ball_ne_top x r), ENNReal.coe_toNNReal (measure_ball_ne_top x' r')]
+    μ.carlesonNnreal (ball x' r') ≤ As A s * μ.carlesonNnreal (ball x r) := by
+  simp only [Measure.carlesonNnreal,← ENNReal.coe_le_coe, coe_mul, ENNReal.coe_toNNReal
+    (carleson_measure_ball_ne_top x r), ENNReal.coe_toNNReal (carleson_measure_ball_ne_top x' r')]
   exact measure_ball_le_of_dist_le' hs h
 
 
@@ -299,11 +300,11 @@
           ≤ μ (ball x (2 * (2 * r))) := μ.mono (closedBall_subset_ball (by linarith))
         _ ≤ A * μ (ball x (2 * r)) := measure_ball_two_le_same x (2 * r)
         _ ≤ A * (A * μ (ball x r)) := mul_le_mul_of_nonneg_left
-          (measure_ball_two_le_same x r) (zero_le _)
+          (measure_ball_two_le_same x r) (by positivity)
         _ = ↑(A ^ 2) * μ (ball x r) := by
           simp only [pow_two, coe_mul,mul_assoc]
         _ ≤ ↑(A ^ 2) * μ (closedBall x r) := mul_le_mul_of_nonneg_left
-          (μ.mono ball_subset_closedBall) (zero_le ((A ^ 2 : ℝ≥0) : ℝ≥0∞))
+          (μ.mono ball_subset_closedBall) (by positivity)
 end Metric
 
 section Normed
```

## Carleson/Legacy212Norm.lean

```diff
--- upstream/Carleson/Legacy212Norm.lean
+++ lean-4.34.1/Carleson/Legacy212Norm.lean
@@ -0,0 +1,28 @@
+import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
+noncomputable section
+open scoped ENNReal NNReal
+namespace MeasureTheory
+variable {α ε : Type*} [MeasurableSpace α] [ENorm ε]
+def legacy212Norm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
+  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f p.toReal μ
+@[simp] theorem legacy212Norm_exponent_zero (f : α → ε) (μ : Measure α) : legacy212Norm f 0 μ = 0 := by simp [legacy212Norm]
+@[simp] theorem legacy212Norm_exponent_top (f : α → ε) (μ : Measure α) : legacy212Norm f ∞ μ = eLpNormEssSup f μ := by simp [legacy212Norm]
+theorem legacy212Norm_eq_eLpNorm' {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} (h0 : p ≠ 0) (ht : p ≠ ∞) :
+    legacy212Norm f p μ = eLpNorm' f p.toReal μ := by simp [legacy212Norm, h0, ht]
+theorem legacy212Norm_nnreal_eq_eLpNorm' {f : α → ε} {p : ℝ≥0} {μ : Measure α} (h0 : p ≠ 0) :
+    legacy212Norm f p μ = eLpNorm' f p μ := by simp [legacy212Norm, h0]
+variable [TopologicalSpace ε]
+theorem legacy212Norm_eq_current {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} (hf : AEStronglyMeasurable f μ) :
+    legacy212Norm f p μ = eLpNorm f p μ := by simp [legacy212Norm, eLpNorm, hf]
+def Legacy212MemLp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
+  AEStronglyMeasurable f μ ∧ legacy212Norm f p μ < ∞
+theorem legacy212MemLp_iff {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} :
+    Legacy212MemLp f p μ ↔ MemLp f p μ := by
+  constructor
+  · intro h
+    change eLpNorm f p μ < ∞
+    rw [← legacy212Norm_eq_current h.1]
+    exact h.2
+  · intro h
+    exact ⟨h.aestronglyMeasurable, by simpa [legacy212Norm_eq_current h.aestronglyMeasurable] using (show eLpNorm f p μ < ∞ from h)⟩
+end MeasureTheory
```

## Carleson/ToMathlib/ENorm.lean

```diff
--- upstream/Carleson/ToMathlib/ENorm.lean
+++ lean-4.34.1/Carleson/ToMathlib/ENorm.lean
@@ -1,3 +1,4 @@
+import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
 import Mathlib.Analysis.Normed.Group.Basic
 import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
 
@@ -7,92 +8,93 @@
 
 variable {α α' E E₁ E₂ F : Type*} [ENorm F]
 
-lemma ENNReal.ofReal_norm [SeminormedAddGroup E] (x : E) : .ofReal ‖x‖ = ‖x‖ₑ := by
-  simp_rw [enorm_eq_nnnorm, ofReal_norm_eq_coe_nnnorm]
+lemma ENNReal.Legacy212_ofReal_norm [SeminormedAddGroup E] (x : E) : .ofReal ‖x‖ = ‖x‖ₑ := by
+  exact _root_.ofReal_norm x
 
-lemma enorm_toReal_le {x : ℝ≥0∞} : ‖x.toReal‖ₑ ≤ x := by simp [← ofReal_norm, ofReal_toReal_le]
+lemma Legacy212_enorm_toReal_le {x : ℝ≥0∞} : ‖x.toReal‖ₑ ≤ x := by simp [← Legacy212_ofReal_norm, ofReal_toReal_le]
 
-@[simp] lemma enorm_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : ‖x.toReal‖ₑ = x := by
-  simp [enorm_eq_nnnorm, hx, ← ofReal_norm_eq_coe_nnnorm]
+@[simp] lemma Legacy212_enorm_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : ‖x.toReal‖ₑ = x := by
+  simpa only [← _root_.ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using ENNReal.ofReal_toReal hx
 
 /-- A type `E` equipped with a continuous map `‖·‖ₑ : E → ℝ≥0∞`.
 Note: do we want to unbundle this (at least separate out `TopologicalSpace E`?)
 Note: not sure if this is the "right" class to add to Mathlib. -/
-class ContinuousENorm (E : Type*) extends ENorm E, TopologicalSpace E where
-  continuous_enorm : Continuous enorm
+class Legacy212_ContinuousENorm (E : Type*) extends ENorm E, TopologicalSpace E where
+  Legacy212_continuous_enorm : Continuous enorm
   -- the topology is somehow defined by the enorm.
 
 /-- An enormed monoid is an additive monoid endowed with a continuous enorm.
 Note: not sure if this is the "right" class to add to Mathlib. -/
-class ENormedAddMonoid (E : Type*) extends ContinuousENorm E, AddMonoid E where
-  enorm_eq_zero : ∀ x : E, ‖x‖ₑ = 0 ↔ x = 0
-  -- enorm_neg : ∀ x y : E, x + y = 0 → ‖x‖ₑ = ‖y‖ₑ -- this is a silly way to write this
-  enorm_add_le : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ
+class Legacy212_ENormedAddMonoid (E : Type*) extends Legacy212_ContinuousENorm E, AddMonoid E where
+  Legacy212_enorm_eq_zero : ∀ x : E, ‖x‖ₑ = 0 ↔ x = 0
+  -- Legacy212_enorm_neg : ∀ x y : E, x + y = 0 → ‖x‖ₑ = ‖y‖ₑ -- this is a silly way to write this
+  Legacy212_enorm_add_le : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ
 
 /-- An enormed monoid is an additive monoid endowed with a continuous enorm.
 Note: not sure if this is the "right" class to add to Mathlib. -/
-class ENormedAddCommMonoid (E : Type*) extends ENormedAddMonoid E, AddCommMonoid E where
+class Legacy212_ENormedAddCommMonoid (E : Type*) extends Legacy212_ENormedAddMonoid E, AddCommMonoid E where
 
 /-- An enormed space is an additive monoid endowed with a continuous enorm.
 Note: not sure if this is the "right" class to add to Mathlib. -/
-class ENormedSpace (E : Type*) extends ENormedAddCommMonoid E, Module ℝ≥0 E where
-  enorm_smul : ∀ (c : ℝ≥0) (x : E), ‖c • x‖ₑ = c • ‖x‖ₑ
+class Legacy212_ENormedSpace (E : Type*) extends Legacy212_ENormedAddCommMonoid E, Module ℝ≥0 E where
+  Legacy212_enorm_smul : ∀ (c : ℝ≥0) (x : E), ‖c • x‖ₑ = c • ‖x‖ₑ
 
-export ENormedAddMonoid (enorm_eq_zero enorm_add_le)
-export ENormedSpace (enorm_smul)
-attribute [simp] enorm_eq_zero enorm_smul
+export Legacy212_ENormedAddMonoid (Legacy212_enorm_eq_zero Legacy212_enorm_add_le)
+export Legacy212_ENormedSpace (Legacy212_enorm_smul)
+attribute [simp] Legacy212_enorm_eq_zero Legacy212_enorm_smul
 
-@[simp] lemma enorm_zero {ε} [ENormedAddMonoid ε] : ‖(0 : ε)‖ₑ = 0 := by simp
+@[simp] lemma Legacy212_enorm_zero {ε} [Legacy212_ENormedAddMonoid ε] : ‖(0 : ε)‖ₑ = 0 := by simp
 
-instance : ENormedSpace ℝ≥0∞ where
+instance : Legacy212_ENormedSpace ℝ≥0∞ where
+  toModule := inferInstance
   enorm := id
-  enorm_eq_zero := by simp
-  -- enorm_neg := by simp
-  enorm_add_le := by simp
+  Legacy212_enorm_eq_zero := by simp
+  -- Legacy212_enorm_neg := by simp
+  Legacy212_enorm_add_le := by simp
   add_comm := by simp [add_comm]
-  continuous_enorm := continuous_id
-  enorm_smul := by simp
+  Legacy212_continuous_enorm := continuous_id
+  Legacy212_enorm_smul := by simp
 
-instance [SeminormedAddGroup E] : ContinuousENorm E where
-  continuous_enorm := ENNReal.continuous_coe.comp continuous_nnnorm
+instance [SeminormedAddGroup E] : Legacy212_ContinuousENorm E where
+  Legacy212_continuous_enorm := ENNReal.continuous_coe.comp continuous_nnnorm
 
-instance [NormedAddGroup E] : ENormedAddMonoid E where
-  enorm_eq_zero := by simp [enorm_eq_nnnorm]
-  -- enorm_neg := by
+instance [NormedAddGroup E] : Legacy212_ENormedAddMonoid E where
+  Legacy212_enorm_eq_zero := by simp [enorm_eq_nnnorm]
+  -- Legacy212_enorm_neg := by
   --   simp (config := {contextual := true}) [← eq_neg_iff_add_eq_zero, enorm_eq_nnnorm]
-  enorm_add_le := by simp [enorm_eq_nnnorm, ← ENNReal.coe_add, nnnorm_add_le]
+  Legacy212_enorm_add_le := by simp [enorm_eq_nnnorm, ← ENNReal.coe_add, nnnorm_add_le]
 
-@[simp] lemma enorm_neg [NormedAddGroup E] (x : E) : ‖-x‖ₑ = ‖x‖ₑ := by
+@[simp] lemma Legacy212_enorm_neg [NormedAddGroup E] (x : E) : ‖-x‖ₑ = ‖x‖ₑ := by
   simp_rw [enorm_eq_nnnorm, nnnorm_neg]
 
-instance [NormedAddCommGroup E] : ENormedAddCommMonoid E where
+instance [NormedAddCommGroup E] : Legacy212_ENormedAddCommMonoid E where
   add_comm := by simp [add_comm]
 
-instance [NormedAddCommGroup E] [NormedSpace ℝ E] : ENormedSpace E where
-  enorm_smul := by simp_rw [enorm_eq_nnnorm, ENNReal.smul_def, NNReal.smul_def, nnnorm_smul]; simp
+instance [NormedAddCommGroup E] [NormedSpace ℝ E] : Legacy212_ENormedSpace E where
+  Legacy212_enorm_smul := by simp_rw [enorm_eq_nnnorm, ENNReal.smul_def, NNReal.smul_def, nnnorm_smul]; simp
 
 namespace MeasureTheory
-section ContinuousENorm
-variable {α E : Type*} {m : MeasurableSpace α} [ContinuousENorm E] {μ : Measure α}
+section Legacy212_ContinuousENorm
+variable {α E : Type*} {m : MeasurableSpace α} [Legacy212_ContinuousENorm E] {μ : Measure α}
 
-export ContinuousENorm (continuous_enorm)
+export Legacy212_ContinuousENorm (Legacy212_continuous_enorm)
 
 protected theorem Continuous.enorm {X : Type*} [TopologicalSpace X] {f : X → E}
     (hf : Continuous f) : Continuous (fun x => (‖f x‖ₑ)) :=
-  continuous_enorm.comp hf
+  Legacy212_continuous_enorm.comp hf
 
-theorem measurable_enorm [MeasurableSpace E] [OpensMeasurableSpace E] :
+theorem Legacy212_measurable_enorm [MeasurableSpace E] [OpensMeasurableSpace E] :
     Measurable (fun a : E => (‖a‖ₑ)) :=
-  continuous_enorm.measurable
+  Legacy212_continuous_enorm.measurable
 
 protected theorem AEMeasurable.enorm [MeasurableSpace E] [OpensMeasurableSpace E] {f : α → E}
     (hf : AEMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ :=
-  measurable_enorm.comp_aemeasurable hf
+  Legacy212_measurable_enorm.comp_aemeasurable hf
 
-protected theorem AEStronglyMeasurable.enorm {f : α → E}
+protected theorem AEStronglyMeasurable.legacy212_enorm {f : α → E}
     (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ :=
-  continuous_enorm.comp_aestronglyMeasurable hf |>.aemeasurable
+  Legacy212_continuous_enorm.comp_aestronglyMeasurable hf |>.aemeasurable
 
-end ContinuousENorm
+end Legacy212_ContinuousENorm
 
 end MeasureTheory
```

## Carleson/WeakType.lean

```diff
--- upstream/Carleson/WeakType.lean
+++ lean-4.34.1/Carleson/WeakType.lean
@@ -1,12 +1,16 @@
+import Carleson.Legacy212Norm
 import Mathlib.MeasureTheory.Integral.MeanInequalities
 import Mathlib.MeasureTheory.Integral.Layercake
-import Mathlib.MeasureTheory.Integral.Lebesgue
+import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
 import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
 import Mathlib.Analysis.SpecialFunctions.Pow.Integral
 import Carleson.ToMathlib.ENorm
 import Carleson.ToMathlib.Misc
 
 noncomputable section
+local instance {E : Type*} [Legacy212_ContinuousENorm E] : ContinuousENorm E where
+  continuous_enorm := Legacy212_ContinuousENorm.Legacy212_continuous_enorm
+
 
 open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function
 
@@ -62,7 +66,7 @@
 def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
   μ { x | t < ‖f x‖ₑ }
 
-@[gcongr]
+@[gcongr only]
 lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ :=
   measure_mono fun _ a ↦ lt_of_le_of_lt h a
 
@@ -84,7 +88,7 @@
   apply measure_mono
   simp_rw [comp_apply, enorm_eq_self, setOf_subset_setOf]
   intro x hx
-  exact hx.trans_le enorm_toReal_le
+  exact hx.trans_le Legacy212_enorm_toReal_le
 
 lemma distribution_add_le_of_enorm {A : ℝ≥0∞}
     (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
@@ -142,7 +146,7 @@
     ContinuousWithinAt (distribution f · μ) (Ioi t₀) t₀ := by
   rcases (eq_top_or_lt_top t₀) with t₀top | t₀nottop
   · rw [t₀top]
-    apply continuousWithinAt_of_not_mem_closure
+    apply continuousWithinAt_of_notMem_closure
     simp
   · unfold ContinuousWithinAt
     rcases (eq_top_or_lt_top (distribution f t₀ μ)) with db_top | db_not_top
@@ -175,7 +179,7 @@
           rw [db_zero] at h₂
           change Icc 0 ε (distribution f z μ)
           rw [nonpos_iff_eq_zero.mp h₂]
-          exact ⟨zero_le 0, zero_le ε⟩
+          exact ⟨(by positivity), (by positivity)⟩
       -- Case: 0 < distribution f t₀ μ
       · obtain ⟨n, wn⟩ :=
           select_neighborhood_distribution t₀ _ (ENNReal.sub_lt_self db_not_top.ne_top
@@ -240,9 +244,7 @@
 lemma eLpNormEssSup_toReal_le {f : α → ℝ≥0∞} :
     eLpNormEssSup (ENNReal.toReal ∘ f) μ ≤ eLpNormEssSup f μ := by
   simp_rw [eLpNormEssSup, enorm_eq_self]
-  apply essSup_mono_ae
-  apply Eventually.of_forall
-  simp [enorm_toReal_le, implies_true]
+  exact essSup_mono_ae (Eventually.of_forall fun x ↦ Legacy212_enorm_toReal_le)
 
 lemma wnorm_toReal_le {f : α → ℝ≥0∞} {p : ℝ≥0∞} :
     wnorm (ENNReal.toReal ∘ f) p μ ≤ wnorm f p μ := by
@@ -254,9 +256,9 @@
 
 end ENorm
 
-section ContinuousENorm
-
-variable [ContinuousENorm ε] [ContinuousENorm ε₁] [ContinuousENorm ε₂] {f : α → ε} {f₁ : α → ε₁}
+section Legacy212_ContinuousENorm
+
+variable [Legacy212_ContinuousENorm ε] [Legacy212_ContinuousENorm ε₁] [Legacy212_ContinuousENorm ε₂] {f : α → ε} {f₁ : α → ε₁}
 
 lemma wnorm'_le_eLpNorm' (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
     wnorm' f p μ ≤ eLpNorm' f p μ := by
@@ -271,20 +273,20 @@
   refine rpow_le_rpow ?_ p0'
   refine le_trans ?_ <| mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const p) (ofNNReal t ^ p)
   gcongr
-  exact setOf_subset_setOf.mpr (fun _ h ↦ h.le)
+  exact fun h ↦ h.le
 
 lemma wnorm_le_eLpNorm (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
-    wnorm f p μ ≤ eLpNorm f p μ := by
+    wnorm f p μ ≤ legacy212Norm f p μ := by
   by_cases h : p = ⊤
-  · simp [h, wnorm, eLpNorm]
+  · simp [h, wnorm, legacy212Norm]
   · have p0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne.symm
-    simpa [h, wnorm, eLpNorm, p0] using wnorm'_le_eLpNorm' hf (toReal_mono h hp)
+    simpa [h, wnorm, legacy212Norm, p0] using wnorm'_le_eLpNorm' hf (toReal_mono h hp)
 
 /-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
 def MemWℒp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
   AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞
 
-lemma Memℒp.memWℒp (hp : 1 ≤ p) (hf : Memℒp f p μ) : MemWℒp f p μ :=
+lemma Legacy212MemLp.memWℒp (hp : 1 ≤ p) (hf : Legacy212MemLp f p μ) : MemWℒp f p μ :=
   ⟨hf.1, wnorm_le_eLpNorm hf.1 hp |>.trans_lt hf.2⟩
 
 lemma MemWℒp_zero : ¬ MemWℒp f 0 μ := by
@@ -322,7 +324,7 @@
   by_cases hC_zero : C = 0
   · simp only [ENNReal.iSup_eq_zero, mul_eq_zero, ENNReal.rpow_eq_zero_iff, inv_neg'', C] at hC_zero
     specialize hC_zero 1
-    simp only [one_ne_zero, ENNReal.coe_one, toReal_nonneg.not_lt, and_false, or_false,
+    simp only [one_ne_zero, ENNReal.coe_one, not_lt_of_ge toReal_nonneg, and_false, or_false,
       false_or] at hC_zero
     exact measure_mono_null (setOf_subset_setOf.mpr fun x hx => hx ▸ one_lt_top) hC_zero.1
   by_contra h
@@ -342,10 +344,10 @@
     nth_rw 1 [← mul_one C]
     rw [ENNReal.mul_div_mul_left _ _ hC_zero h2.ne_top, div_rpow_of_nonneg _ _ toReal_nonneg,
       ENNReal.rpow_inv_rpow hp_toReal_zero, ENNReal.one_rpow, one_div,
-        ENNReal.inv_div (Or.inr two_ne_top) (Or.inr (NeZero.ne' 2).symm)]
+        ENNReal.inv_div (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞)) (Or.inr (NeZero.ne' 2).symm)]
   have h6 : μ A = 0 := by
     convert (fun hh ↦ ENNReal.half_lt_self hh (ne_top_of_le_ne_top (rpow_ne_top_of_nonneg
-      toReal_nonneg ((div_one C).symm ▸ h2.ne_top)) (h4 1))).mt h5.not_lt
+      toReal_nonneg ((div_one C).symm ▸ h2.ne_top)) (h4 1))).mt (not_lt_of_ge h5)
     tauto
   exact h h6
 
@@ -356,7 +358,7 @@
 and constant `c`.  -/
 def HasWeakType (T : (α → ε₁) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
     (c : ℝ≥0) : Prop :=
-  ∀ f : α → ε₁, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ
+  ∀ f : α → ε₁, Legacy212MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * legacy212Norm f p μ
 
 /-- An operator has strong type (p, q) if it is bounded as an operator on `L^p → L^q`.
 `HasStrongType T p p' μ ν c` means that `T` has strong type (p, p') w.r.t. measures `μ`, `ν`
@@ -364,17 +366,17 @@
 def HasStrongType {α α' : Type*}
     {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
     (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
-  ∀ f : α → ε₁, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ
+  ∀ f : α → ε₁, Legacy212MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ legacy212Norm (T f) p' ν ≤ c * legacy212Norm f p μ
 
 /-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
 w.r.t. the L^2 norm, but weaker in general. -/
 def HasBoundedStrongType {α α' : Type*} [Zero ε₁]
     {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
     (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
-  ∀ f : α → ε₁, Memℒp f p μ → eLpNorm f ∞ μ < ∞ → μ (support f) < ∞ →
-  AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ
-
-lemma HasWeakType.memWℒp (h : HasWeakType T p p' μ ν c) (hf₁ : Memℒp f₁ p μ) :
+  ∀ f : α → ε₁, Legacy212MemLp f p μ → legacy212Norm f ∞ μ < ∞ → μ (support f) < ∞ →
+  AEStronglyMeasurable (T f) ν ∧ legacy212Norm (T f) p' ν ≤ c * legacy212Norm f p μ
+
+lemma HasWeakType.memWℒp (h : HasWeakType T p p' μ ν c) (hf₁ : Legacy212MemLp f₁ p μ) :
     MemWℒp (T f₁) p' ν :=
   ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩
 
@@ -383,8 +385,8 @@
   fun f hf ↦ ⟨(h f hf).1.ennreal_toReal, wnorm_toReal_le.trans (h f hf).2 ⟩
 
 
-lemma HasStrongType.memℒp (h : HasStrongType T p p' μ ν c) (hf₁ : Memℒp f₁ p μ) :
-    Memℒp (T f₁) p' ν :=
+lemma HasStrongType.memℒp (h : HasStrongType T p p' μ ν c) (hf₁ : Legacy212MemLp f₁ p μ) :
+    Legacy212MemLp (T f₁) p' ν :=
   ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩
 
 lemma HasStrongType.hasWeakType (hp' : 1 ≤ p')
@@ -393,15 +395,15 @@
 
 
 lemma HasBoundedStrongType.memℒp [Zero ε₁] (h : HasBoundedStrongType T p p' μ ν c)
-    (hf₁ : Memℒp f₁ p μ) (h2f₁ : eLpNorm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞) :
-    Memℒp (T f₁) p' ν :=
+    (hf₁ : Legacy212MemLp f₁ p μ) (h2f₁ : legacy212Norm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞) :
+    Legacy212MemLp (T f₁) p' ν :=
   ⟨(h f₁ hf₁ h2f₁ h3f₁).1, h f₁ hf₁ h2f₁ h3f₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩
 
 lemma HasStrongType.hasBoundedStrongType [Zero ε₁] (h : HasStrongType T p p' μ ν c) :
     HasBoundedStrongType T p p' μ ν c :=
   fun f hf _ _ ↦ h f hf
 
-end ContinuousENorm
+end Legacy212_ContinuousENorm
 
 section NormedGroup
 
@@ -409,11 +411,11 @@
 
 variable {f g : α → ε}
 section
-variable [ContinuousENorm ε]
+variable [Legacy212_ContinuousENorm ε]
 
 lemma distribution_eq_nnnorm {f : α → E} : distribution f t μ =  μ { x | t < ‖f x‖₊ } := rfl
 
-@[gcongr]
+@[gcongr only]
 lemma distribution_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
     distribution f t μ ≤ distribution g t μ := by
   have h₀ : {x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ} ⊆ {x | ¬‖f x‖ₑ ≤ ‖g x‖ₑ} := fun x ↦ by
@@ -425,7 +427,7 @@
     _ = μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ}) := by rw [measure_mono_null h₀ h, add_zero]
     _ ≤ _ := by apply measure_mono; simp
 
-@[gcongr]
+@[gcongr only]
 lemma distribution_mono (h₁ : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) (h₂ : t ≤ s) :
     distribution f s μ ≤ distribution g t μ :=
   (distribution_mono_left h₁).trans (distribution_mono_right h₂)
@@ -439,8 +441,9 @@
   have h₀ : ofNNReal ‖c‖₊ ≠ 0 := ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hc)
   congr with x
   simp only [Pi.smul_apply, mem_setOf_eq]
-  rw [← @ENNReal.mul_lt_mul_right (t / ‖c‖₊) _ (‖c‖₊) h₀ coe_ne_top,
-    ENNNorm_absolute_homogeneous _, mul_comm, ENNReal.div_mul_cancel h₀ coe_ne_top]
+  rw [ENNNorm_absolute_homogeneous _]
+  rw [ENNReal.div_lt_iff (Or.inl h₀) (Or.inl coe_ne_top)]
+  rw [mul_comm]
 
 lemma distribution_add_le' {A : ℝ≥0∞} {g₁ g₂ : α → ε}
     (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
@@ -451,11 +454,15 @@
 lemma HasStrongType.const_smul {𝕜 E' α α' : Type*} [NormedAddCommGroup E']
     {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} {T : (α → ε) → (α' → E')}
     {p p' : ℝ≥0∞} {μ : Measure α} {ν : Measure α'} {c : ℝ≥0} (h : HasStrongType T p p' μ ν c)
-    [NormedRing 𝕜] [MulActionWithZero 𝕜 E'] [BoundedSMul 𝕜 E'] (k : 𝕜) :
+    [NormedRing 𝕜] [MulActionWithZero 𝕜 E'] [IsBoundedSMul 𝕜 E'] (k : 𝕜) :
     HasStrongType (k • T) p p' μ ν (‖k‖₊ * c) := by
-  refine fun f hf ↦
-    ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, eLpNorm_const_smul_le.trans ?_⟩
-  simp only [ENNReal.smul_def, smul_eq_mul, coe_mul, mul_assoc]
+  refine fun f hf ↦ ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, ?_⟩
+  change legacy212Norm (k • T f) p' ν ≤ _
+  rw [legacy212Norm_eq_current ((h f hf).1.const_smul k)]
+  have hb := eLpNorm_const_smul_le (f := T f) (c := k) (p := p') (μ := ν)
+  rw [← legacy212Norm_eq_current (h f hf).1] at hb
+  apply hb.trans
+  simp only [ENNReal.smul_def, smul_eq_mul, coe_mul, mul_assoc, enorm_eq_nnnorm]
   gcongr
   exact (h f hf).2
 
@@ -467,14 +474,14 @@
 
 end
 
-lemma distribution_add_le [ENormedAddMonoid ε] :
+lemma distribution_add_le [Legacy212_ENormedAddMonoid ε] :
     distribution (f + g) (t + s) μ ≤ distribution f t μ + distribution g s μ :=
   calc
     _ ≤ μ ({x | t < ↑‖f x‖ₑ} ∪ {x | s < ↑‖g x‖ₑ}) := by
       refine measure_mono fun x h ↦ ?_
       simp only [mem_union, mem_setOf_eq, Pi.add_apply] at h ⊢
       contrapose! h
-      exact (enorm_add_le _ _).trans (add_le_add h.1 h.2)
+      exact (Legacy212_enorm_add_le _ _).trans (add_le_add h.1 h.2)
     _ ≤ _ := measure_union_le _ _
 
 lemma _root_.ContinuousLinearMap.distribution_le {f : α → E₁} {g : α → E₂} :
@@ -493,14 +500,14 @@
           _ ≤ ↑‖L (f z)‖₊ * ↑‖g z‖₊ := ContinuousLinearMap.le_opNNNorm (L (f z)) (g z)
           _ ≤ ‖L‖₊ * ‖f z‖₊ * ‖g z‖₊ :=
             mul_le_mul' (ContinuousLinearMap.le_opNNNorm L (f z)) (by rfl)
-      _ ≤ _ := mul_le_mul' (mul_le_mul_left' hz.1 ↑‖L‖₊) hz.2
+      _ ≤ _ := mul_le_mul' (mul_le_mul_right hz.1 _) hz.2
   calc
     _ ≤ μ ({x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊}) := measure_mono h₀
     _ ≤ _ := measure_union_le _ _
 
 section BorelSpace
 
-variable [ContinuousENorm ε] [MeasurableSpace E] [BorelSpace E]
+variable [Legacy212_ContinuousENorm ε] [MeasurableSpace E] [BorelSpace E]
 
 /-- The layer-cake theorem, or Cavalieri's principle for functions into a normed group. -/
 lemma lintegral_norm_pow_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
@@ -511,29 +518,35 @@
     (Eventually.of_forall fun x ↦ norm_nonneg _) hf.norm hp
   simp only [enorm_eq_nnnorm, norm_nonneg, ← ofReal_rpow_of_nonneg, mul_comm (μ _), ne_eq,
     ofReal_ne_top, not_false_eq_true, ← lintegral_const_mul', ← mul_assoc,
-    ← ofReal_norm_eq_coe_nnnorm, ofReal_mul, distribution, h2p] at this ⊢
+    ← ofReal_norm, ofReal_mul, distribution, h2p] at this ⊢
   convert this using 1
-  refine setLIntegral_congr_fun measurableSet_Ioi (Eventually.of_forall fun x hx ↦ ?_)
-  simp_rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hx)]
-
-/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`. -/
+  · simp only [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
+  · apply setLIntegral_congr_fun measurableSet_Ioi
+    intro t ht
+    dsimp only
+    congr 2
+    ext x
+    simp only [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
+    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)
+
+/-- The layer-cake theorem, or Cavalieri's principle, written using `legacy212Norm`. -/
 lemma eLpNorm_pow_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ≥0} (hp : 0 < p) :
-    eLpNorm f p μ ^ (p : ℝ) =
+    legacy212Norm f p μ ^ (p : ℝ) =
     ∫⁻ t in Ioi (0 : ℝ), p * ENNReal.ofReal (t ^ ((p : ℝ) - 1)) * distribution f (.ofReal t) μ := by
   have h2p : 0 < (p : ℝ) := hp
-  simp_rw [eLpNorm_nnreal_eq_eLpNorm' hp.ne', eLpNorm', one_div, ← ENNReal.rpow_mul,
+  simp_rw [legacy212Norm_nnreal_eq_eLpNorm' hp.ne', eLpNorm', one_div, ← ENNReal.rpow_mul,
     inv_mul_cancel₀ h2p.ne', ENNReal.rpow_one, lintegral_norm_pow_eq_distribution hf h2p,
     ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal]
 
-/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`, without
+/-- The layer-cake theorem, or Cavalieri's principle, written using `legacy212Norm`, without
     taking powers. -/
 lemma eLpNorm_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
-    eLpNorm f (.ofReal p) μ =
+    legacy212Norm f (.ofReal p) μ =
     (ENNReal.ofReal p  * ∫⁻ t in Ioi (0 : ℝ), distribution f (.ofReal t) μ *
         ENNReal.ofReal (t ^ (p - 1)) ) ^ p⁻¹ := by
-  unfold eLpNorm
+  unfold legacy212Norm
   split_ifs with sgn_p sz_p
-  · exact False.elim (not_le_of_lt hp (ofReal_eq_zero.mp sgn_p))
+  · exact False.elim (not_le.mpr hp (ofReal_eq_zero.mp sgn_p))
   · exact False.elim (coe_ne_top sz_p)
   · unfold eLpNorm'
     rw [toReal_ofReal (le_of_lt hp), one_div]
@@ -549,7 +562,12 @@
   have h2p : 0 < p + 1 := by linarith
   have h3p : 0 ≤ p + 1 := by linarith
   have h4p : p + 1 ≠ 0 := by linarith
-  simp [*, lintegral_norm_pow_eq_distribution, ← lintegral_const_mul', ← ofReal_mul, ← mul_assoc]
+  rw [ENNReal.ofReal_inv_of_pos h2p]
+  rw [lintegral_norm_pow_eq_distribution hf h2p, ← lintegral_const_mul' _ _ (by simp [h2p])]
+  apply setLIntegral_congr_fun measurableSet_Ioi
+  intro t ht
+  dsimp only
+  rw [add_sub_cancel_right, ENNReal.ofReal_mul h3p, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (a := ENNReal.ofReal (p+1)) (by positivity) ENNReal.ofReal_ne_top, one_mul]
 
 end BorelSpace
```

## Carleson/Defs.lean

```diff
--- upstream/Carleson/Defs.lean
+++ lean-4.34.1/Carleson/Defs.lean
@@ -6,6 +6,7 @@
 
 open MeasureTheory Measure NNReal Metric Complex Set TopologicalSpace Bornology Function
 open scoped ENNReal
+set_option exponentiation.threshold 2048
 noncomputable section
 
 -- todo: rename and protect `Real.RCLike`
@@ -64,11 +65,11 @@
 instance : Coe (Θ X) C(X, 𝕜) := ⟨FunctionDistances.coeΘ⟩
 instance : FunLike (Θ X) X 𝕜 where
   coe := fun f ↦ (f : C(X, 𝕜))
-  coe_injective' _ _ hfg := FunctionDistances.coeΘ_injective fun x ↦ congrFun hfg x
+  coe_injective _ _ hfg := FunctionDistances.coeΘ_injective fun x ↦ congrFun hfg x
 instance : ContinuousMapClass (Θ X) X 𝕜 := ⟨fun f ↦ (f : C(X, 𝕜)).2⟩
 
 set_option linter.unusedVariables false in
-@[nolint unusedArguments]
+@[nolint unusedArguments, reducible]
 def WithFunctionDistance (x : X) (r : ℝ) := Θ X
 
 variable {x : X} {r : ℝ}
@@ -92,7 +93,7 @@
 /-- A set `Θ` of (continuous) functions is compatible. `A` will usually be `2 ^ a`. -/
 class CompatibleFunctions (𝕜 : outParam Type*) (X : Type u) (A : outParam ℕ)
   [RCLike 𝕜] [PseudoMetricSpace X] extends FunctionDistances 𝕜 X where
-  eq_zero : ∃ o : X, ∀ f : Θ, f o = 0
+  eq_zero : ∃ o : X, ∀ f : Θ, coeΘ f o = 0
   /-- The distance is bounded below by the local oscillation. (1.0.7) -/
   localOscillation_le_cdist {x : X} {r : ℝ} {f g : Θ} :
     localOscillation (ball x r) (coeΘ f) (coeΘ g) ≤ ENNReal.ofReal (dist_{x, r} f g)
@@ -135,7 +136,7 @@
 
 export CompatibleFunctions (localOscillation_le_cdist cdist_mono cdist_le le_cdist)
 
-lemma dist_congr [FunctionDistances 𝕜 X] {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ X}
+lemma carleson_dist_congr [FunctionDistances 𝕜 X] {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ X}
     (e₁ : x₁ = x₂) (e₂ : r₁ = r₂) : dist_{x₁, r₁} f g = dist_{x₂, r₂} f g := by congr
 
 variable (X) in
@@ -330,9 +331,9 @@
   | succ k ih =>
     trans 2 * dist_{x, (defaultA a) ^ k * r} f g
     · rw [pow_succ', mul_assoc]
-      exact (mul_le_mul_left zero_lt_two).mpr ih
+      exact (mul_le_mul_of_nonneg_left ih (by positivity))
     · convert le_cdist (ball_subset_ball _) using 1
-      · exact dist_congr rfl (by rw [← mul_assoc, pow_succ'])
+      · exact carleson_dist_congr rfl (by rw [← mul_assoc, pow_succ'])
       · nth_rw 1 [← one_mul ((defaultA a) ^ k * r)]; gcongr
         rw [← Nat.cast_one, Nat.cast_le]; exact Nat.one_le_two_pow
 
@@ -343,9 +344,9 @@
   | succ k ih =>
     trans defaultA a * dist_{x, 2 ^ k * r} f g
     · convert cdist_le _ using 1
-      · exact dist_congr rfl (by ring)
+      · exact carleson_dist_congr rfl (by ring)
       · rw [dist_self]; positivity
-    · replace ih := (mul_le_mul_left (show 0 < (defaultA a : ℝ) by positivity)).mpr ih
+    · replace ih := (mul_le_mul_of_nonneg_left ih (show 0 ≤ (defaultA a : ℝ) by positivity))
       rwa [← mul_assoc, ← pow_succ'] at ih
 
 lemma ballsCoverBalls_iterate_nat {x : X} {d r : ℝ} {n : ℕ} :
@@ -420,7 +421,7 @@
     _ = 2 ^ (5) := by rfl
     _ ≤ 2 ^ (100 * 4 ^ 2) := Nat.le_of_ble_eq_true (by norm_num)
     _ ≤ 2 ^ (100 * a ^ 2) := Nat.pow_le_pow_right (by norm_num)
-      (mul_le_mul_of_nonneg_left (Nat.pow_le_pow_of_le_left this 2) (by norm_num))
+      (mul_le_mul_of_nonneg_left (Nat.pow_le_pow_left this 2) (by norm_num))
 
 -- used in 4.1.3 (`I3_prop_3_1`)
 lemma eight_le_realD : (8 : ℝ) ≤ defaultD a := by
@@ -639,7 +640,7 @@
     have : z ≠ z' → Disjoint (g z) (g z') := g_pd hz hz'
     rw [← e, Finset.disjoint_self_iff_empty] at this
     exact not_ne_iff.mp <| this.mt <| Finset.nonempty_iff_ne_empty.mp (g_ne z hz)
-  have g_subset : g '' 𝓩 ⊆ 𝓩'.powerset.toSet := fun gz hgz ↦ by
+  have g_subset : g '' 𝓩 ⊆ (↑𝓩'.powerset : Set (Finset _)) := fun gz hgz ↦ by
     rw [mem_image] at hgz
     obtain ⟨z, hz⟩ := hgz
     simp_rw [Finset.coe_powerset, mem_preimage, mem_powerset_iff, Finset.coe_subset, ← hz.2, g,
@@ -668,3 +669,9 @@
   obtain ⟨f𝓩, c𝓩⟩ := finite_and_mk_le_of_le_dist h𝓩 h2𝓩
   lift 𝓩 to Finset (Θ X) using f𝓩
   simpa using c𝓩
+
+namespace Real
+structure IsConjExponent (p q : ℝ) : Prop where
+  one_lt : 1 < p
+  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1
+end Real
```
