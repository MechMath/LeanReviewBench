# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

The following exact diffs retain the recorded compatibility choices. Source hash and import-relocation checks do not prove global equivalence of the historical and modern library environments.

## EconCSLib/Foundations/Probability/RealDistribution.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/RealDistribution.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/RealDistribution.lean
@@ -289,7 +289,7 @@
         (by
           refine ⟨a + 1, by linarith, ?_⟩
           exact measure_ne_top μ (Ioc a (a + 1)))
-    simpa [h_inter_empty] using h
+    simpa only [h_inter_empty, Function.comp_def, measure_empty] using h
   have hreal :
       Tendsto (fun b => (μ (Ioc a b)).toReal) (𝓝[>] a) (𝓝 0) :=
     (ENNReal.tendsto_toReal (by simp)).comp hmeasure
```

## LMMS04FairDivision/Theorem31QueryLowerBound.lean

```diff
--- upstream/LMMS04FairDivision/Theorem31QueryLowerBound.lean
+++ lean-4.34.1/LMMS04FairDivision/Theorem31QueryLowerBound.lean
@@ -215,7 +215,7 @@
   · have hsum :
         u.val (A (0 : LMMS31Agent)) +
           u.val (A (1 : LMMS31Agent)) = 1 := by
-      simpa [hA1] using
+      simpa only [hA1, Finset.compl_eq_univ_sdiff] using
         u.complement_sum_of_card_eq (A (0 : LMMS31Agent)) heq
     have hueq :
         u.val (A (0 : LMMS31Agent)) =
```

## LMMS04FairDivision/Theorem34BoundedOptimal.lean

```diff
--- upstream/LMMS04FairDivision/Theorem34BoundedOptimal.lean
+++ lean-4.34.1/LMMS04FairDivision/Theorem34BoundedOptimal.lean
@@ -173,7 +173,7 @@
     exact
       lt_of_lt_of_le hleft_lt_next
         (le_trans hnext_le_primary (Nat.le_add_right _ _))
-  · dsimp
+  · try dsimp
     rw [hprimary_eq]
     exact Nat.add_lt_add_left hsecondary_lt _
```

## LMMS04FairDivision/MainTheorems.lean

```diff
--- upstream/LMMS04FairDivision/MainTheorems.lean
+++ lean-4.34.1/LMMS04FairDivision/MainTheorems.lean
@@ -4301,7 +4301,7 @@
     have hk_spec := Classical.choose_spec (hinterval g hglow)
     have hk_fin_eq : (⟨k, hk_spec.1⟩ : Fin N) = e i := by
       have hcong := congrArg e howner_eq
-      simpa [owner, hglow, e, k] using hcong
+      simpa only [owner, dif_pos hglow, Equiv.apply_symm_apply, k] using hcong
     have hk_eq_idx : k = idx := by
       exact congrArg Fin.val hk_fin_eq
     have hk_spec_k :
@@ -7120,7 +7120,7 @@
             Finset (paper_lmms_theorem_3_3_roundedSupplyItem lowSupply)).filter
             (fun item => lowIndex item = k)).card =
           lowSupply k := by
-      simpa [lowSupply, lowIndex] using
+      exact
         paper_lmms_theorem_3_3_roundedGoodsSupplyOfSupply_eq
           (Theorem33.lowGoodsAggregatedSupply L lambda
             (lowGoods.sum sourceValue)) k
@@ -9672,7 +9672,7 @@
     have hcounts_raw :=
       paper_lmms_isAllocationOf_sum_bundle_index_counts_eq_goods_count
         (A := A) (goods := goods) halloc indexOf k
-    simpa [typeOf] using hcounts_raw
+    exact hcounts_raw
   simpa [p, itemValue] using
     (paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_supply_type_assignment
       (L := L) (LR := LR) (lambda := lambda) (maxCount := maxCount)
@@ -9890,23 +9890,18 @@
       typedIndex A halloc hlambda hL hcap
       (by
         intro i
-        simpa [typedItem, typedIndex,
-          paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue]
-          using hwindow i)
+        exact hwindow i)
   exact
     { pair_mem := by
-        simpa [typedItem, typedIndex,
-          paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue] using
+        exact
           cert.pair_mem
       typeMultiplicity := cert.typeMultiplicity
       zeroOutsideWindow := by
         intro t ht
         exact cert.zeroOutsideWindow t (by
-          simpa [typedItem, typedIndex,
-            paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue] using ht)
+          exact ht)
       allPlayersAssigned := by
-        simpa [typedItem, typedIndex,
-          paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue] using
+        exact
           cert.allPlayersAssigned
       allGoodsAssigned := by
         intro k
@@ -10479,9 +10474,9 @@
     itemToDemandTotal.subtypeEquiv (fun s => by
       constructor
       · intro h
-        simpa [itemToDemandTotal] using h
+        exact h
       · intro h
-        simpa [itemToDemandTotal] using h)
+        exact h)
   let eItem :
       {item : Item // owner item = i ∧ indexOf item = k} ≃
         {d : TotalDemandSlot // d.2.1 = i ∧ d.1 = k} :=
@@ -10623,7 +10618,7 @@
   exact
     ⟨typeOf, A, halloc, htypes, hmultiplicity, hcounts,
       fun i => by
-        simpa [paper_lmms_theorem_3_3_roundedSupplyValue] using hbounded i⟩
+        exact hbounded i⟩
 
 /--
 Full finite realization of a capped concrete IP over the provenance-carrying
@@ -10703,8 +10698,7 @@
         intro i k
         simpa [typedItem, typedIndex] using hcounts i k,
       fun i => by
-        simpa [typedItem, typedIndex,
-          paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue] using
+        exact
           hbounded i⟩
 
 /--
@@ -10925,7 +10919,7 @@
       supply ip A halloc typeOf hmultiplicity
       (fun i =>
         by
-          simpa [paper_lmms_theorem_3_3_roundedSupplyValue] using
+          exact
             paper_lmms_theorem_3_3_commonLoad_eq_roundedBundleTypeLoad_of_bundle_index_counts
               (L := L)
               (paper_lmms_theorem_3_3_roundedSupplyIndexOf
@@ -11070,7 +11064,7 @@
       highGoods lowGoods sourceValue indexOf ip A halloc typeOf hmultiplicity
       (fun i =>
         by
-          simpa [paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue] using
+          exact
             paper_lmms_theorem_3_3_commonLoad_eq_roundedBundleTypeLoad_of_bundle_index_counts
               (L := L)
               (paper_lmms_theorem_3_3_typedCombinedHighLowSupplyIndexOf
@@ -11172,7 +11166,7 @@
       (∑ i : SourceAgent, (typeOf i).count k) =
           paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods typedIndex
             (Finset.univ : Finset typedItem) k := by
-        simpa [typeOf] using hcounts
+        exact hcounts
       _ =
           paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
             Theorem33.lowGoodsAggregatedSupply L lambda
@@ -11257,15 +11251,13 @@
       paper_lmms_theorem_3_3_roundedBundleTypeOfBundle_load_eq_sum
         (L := L) typedIndex (A i)
   · intro i
-    simpa [typeOf, typedItem, typedIndex,
-      paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_exact_rounded_allocation_types_in_min_max_window
         (SourceItem := typedItem) (L := L) (lambda := lambda)
         typedIndex A hlambda hL
         (by
           intro j
-          simpa [typedItem, typedIndex,
-            paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue] using
+          exact
             hwindow j)
         i
   · intro k
@@ -11278,7 +11270,7 @@
       (∑ i : SourceAgent, (typeOf i).count k) =
           paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods typedIndex
             (Finset.univ : Finset typedItem) k := by
-        simpa [typeOf] using hcounts
+        exact hcounts
       _ =
           paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
             Theorem33.lowGoodsAggregatedSupply L lambda
@@ -11417,7 +11409,7 @@
       (∑ i : SourceAgent, (typeOf i).count k) =
           paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods typedIndex
             (Finset.univ : Finset typedItem) k := by
-        simpa [typeOf] using hcounts
+        exact hcounts
       _ =
           paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
             Theorem33.lowGoodsAggregatedSupply L lambda
@@ -11476,7 +11468,7 @@
         (A i)
   refine ⟨typeOf, ?_, ?_⟩
   · intro i
-    simpa [typeOf] using
+    exact
       paper_lmms_theorem_3_3_exact_rounded_allocation_types_in_min_max_window
         (SourceItem := paper_lmms_theorem_3_3_roundedSupplyItem supply)
         (L := L) (lambda := lambda)
@@ -11501,7 +11493,7 @@
               (supply := supply))
             (Finset.univ :
               Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)) k := by
-        simpa [typeOf] using hcounts
+        exact hcounts
       _ = supply k :=
         paper_lmms_theorem_3_3_roundedGoodsSupplyOfSupply_eq supply k
 
@@ -11671,7 +11663,7 @@
               (supply := supply))
             (Finset.univ :
               Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)) k := by
-        simpa [typeOf] using hcounts_raw
+        exact hcounts_raw
       _ = supply k :=
         paper_lmms_theorem_3_3_roundedGoodsSupplyOfSupply_eq supply k
   simpa [p, itemValue] using
@@ -12263,13 +12255,9 @@
         A halloc hlambda hL
         (by
           intro i
-          simpa [paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue,
-            paper_lmms_theorem_3_3_typedCombinedHighLowSupplyIndexOf]
-            using hwindow i))
+          exact hwindow i))
   refine ⟨search, ?_⟩
-  simpa [Theorem33.roundedValuePairRatio, Theorem34.loadRatio,
-    paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue,
-    paper_lmms_theorem_3_3_typedCombinedHighLowSupplyIndexOf] using hsearch
+  exact hsearch
 
 /--
 Theorem 3.3 exact typed combined high/low search bridge with the final
@@ -12507,8 +12495,7 @@
       A halloc hlambda hL
       (by
         intro i
-        simpa [paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue]
-          using hwindow i)
+        exact hwindow i)
   obtain ⟨search, hsearch⟩ :=
     paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_exact_bounded_typed_combined_high_low_allocation
       (L := L) (lambda := lambda)
@@ -12677,8 +12664,7 @@
       A halloc hlambda hL
       (by
         intro i
-        simpa [paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue]
-          using hwindow i)
+        exact hwindow i)
   obtain ⟨search, hsearch⟩ :=
     paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_exact_bounded_typed_combined_high_low_allocation
       (L := L) (lambda := lambda)
@@ -13122,10 +13108,8 @@
       typeOfI ∈ Theorem33.roundedAdmissibleTypeSet L lambda :=
     Theorem33.roundedBundleType_mem_roundedAdmissibleTypeSet_of_load_window
       hlambda hL typeOfI
-      (by simpa [M, paper_lmms_theorem_3_3_roundedModelOfIndex, hload_common]
-        using (cert.2 i).1)
-      (by simpa [M, paper_lmms_theorem_3_3_roundedModelOfIndex, hload_common]
-        using (cert.2 i).2)
+      (by rw [hload_common]; exact (cert.2 i).1)
+      (by rw [hload_common]; exact (cert.2 i).2)
   have hmin_le :
       Theorem33.minAllocationLoad M A ≤
         Theorem33.roundedBundleTypeLoad L typeOfI := by
@@ -14746,7 +14730,7 @@
             Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)) →
           0 < itemValue g := by
     intro g _hg
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_pos
         (L := L) (lambda := lambda) hlambda hL g
   have hgoods_lt :
@@ -14756,7 +14740,7 @@
             Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)) →
           itemValue g < L := by
     intro g _hg
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_top_supply_eq_zero
         (L := L) (lambda := lambda) hlambda hL htop_zero g
   rcases
@@ -15033,7 +15017,7 @@
             Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)) →
           0 < itemValue g := by
     intro g _hg
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_pos
         (L := L) (lambda := lambda) hlambda hL g
   have hgoods_lt :
@@ -15043,7 +15027,7 @@
             Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)) →
           itemValue g < L := by
     intro g _hg
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_top_supply_eq_zero
         (L := L) (lambda := lambda) hlambda hL htop_zero g
   rcases
@@ -16145,7 +16129,7 @@
             Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)) →
           0 < itemValue g := by
     intro g _hg
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_pos
         (L := L) (lambda := lambda) hlambda hL g
   have hgoods_lt :
@@ -16155,7 +16139,7 @@
             Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)) →
           itemValue g < L := by
     intro g _hg
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_top_supply_eq_zero
         (L := L) (lambda := lambda) hlambda hL htop_zero g
   have howner_univ :
@@ -16182,10 +16166,10 @@
       (by simpa [itemValue] using hB_window)
   refine ⟨B, hB_alloc, hB_nonempty, ?_, ?_, search, ?_⟩
   · intro C hC_alloc hC_nonempty
-    simpa [paper_lmms_theorem_3_3_roundedSupplyAllocationRatio, itemValue] using
+    exact
       hB_opt C hC_alloc hC_nonempty
   · simpa [itemValue] using hB_window
-  · simpa [paper_lmms_theorem_3_3_roundedSupplyAllocationRatio, itemValue] using
+  · exact
       hsearch
 
 /--
@@ -16712,14 +16696,14 @@
       ∀ item : paper_lmms_theorem_3_3_roundedSupplyItem supply,
         0 < itemValue item := by
     intro item
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_pos
         (L := L) (lambda := lambda) hlambda hL item
   have hitem_lt :
       ∀ item : paper_lmms_theorem_3_3_roundedSupplyItem supply,
         itemValue item < L := by
     intro item
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_top_supply_eq_zero
         (L := L) (lambda := lambda) hlambda hL htop_zero item
   have htotal :
@@ -16731,7 +16715,7 @@
         (L := L) (lambda := lambda) supply
     exact
       (by
-        simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+        exact
           hsum.trans hsupply_average)
   rcases
       paper_lmms_exists_surjective_owner_of_total_strictly_small_positive_values
@@ -16871,14 +16855,14 @@
       ∀ item : paper_lmms_theorem_3_3_roundedSupplyItem supply,
         0 < itemValue item := by
     intro item
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_pos
         (L := L) (lambda := lambda) hlambda hL item
   have hitem_lt :
       ∀ item : paper_lmms_theorem_3_3_roundedSupplyItem supply,
         itemValue item < L := by
     intro item
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_top_supply_eq_zero
         (L := L) (lambda := lambda) hlambda hL htop_zero item
   have htotal :
@@ -16890,7 +16874,7 @@
         (L := L) (lambda := lambda) supply
     exact
       (by
-        simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+        exact
           hsum.trans hsupply_average)
   exact
     Exists.elim
@@ -16936,14 +16920,14 @@
       ∀ item : paper_lmms_theorem_3_3_roundedSupplyItem supply,
         0 < itemValue item := by
     intro item
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_pos
         (L := L) (lambda := lambda) hlambda hL item
   have hitem_lt :
       ∀ item : paper_lmms_theorem_3_3_roundedSupplyItem supply,
         itemValue item < L := by
     intro item
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_top_supply_eq_zero
         (L := L) (lambda := lambda) hlambda hL htop_zero item
   have htotal :
@@ -16955,7 +16939,7 @@
         (L := L) (lambda := lambda) supply
     exact
       (by
-        simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+        exact
           hsum.trans hsupply_average)
   exact
     Exists.elim
@@ -17021,7 +17005,7 @@
       ∀ item : paper_lmms_theorem_3_3_roundedSupplyItem supply,
         0 < itemValue item := by
     intro item
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       paper_lmms_theorem_3_3_roundedSupplyValue_pos
         (L := L) (lambda := lambda) hlambda hL item
   have hitem_lt :
@@ -17029,7 +17013,7 @@
         itemValue item < LR := by
     intro item
     have hltL : itemValue item < L := by
-      simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+      exact
         paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_top_supply_eq_zero
           (L := L) (lambda := lambda) hlambda hL htop_zero item
     exact lt_of_lt_of_le hltL hbase_le_avg
@@ -17042,7 +17026,7 @@
         (L := L) (lambda := lambda) supply
     exact
       (by
-        simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+        exact
           hsum.trans hsupply_average)
   rcases
       paper_lmms_exists_surjective_owner_of_total_strictly_small_positive_values
@@ -17092,11 +17076,10 @@
     ⟨B, hB_alloc, hB_nonempty, hB_opt, hB_window⟩
   refine ⟨B, hB_alloc, hB_nonempty, ?_, ?_⟩
   · intro C hC_alloc hC_nonempty
-    simpa [paper_lmms_theorem_3_3_roundedSupplyAllocationRatio, itemValue,
-      paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       hB_opt C hC_alloc hC_nonempty
   · intro i
-    simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+    exact
       hB_window i
 
 /--
@@ -17200,10 +17183,8 @@
     exact
       Theorem33.roundedBundleType_mem_roundedAdmissibleTypeSetWithCap_of_load_window
         hlambda hL hcap (typeOf i)
-        (by simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue,
-          hload_eq i] using (hB_window i).1)
-        (by simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue,
-          hload_eq i] using (hB_window i).2)
+        (by rw [hload_eq i]; exact (hB_window i).1)
+        (by rw [hload_eq i]; exact (hB_window i).2)
   have htypes :
       ∀ i : SourceAgent,
         typeOf i ∈
@@ -17248,7 +17229,7 @@
               (supply := supply))
             (Finset.univ :
               Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)) k := by
-        simpa [typeOf, paper_lmms_theorem_3_3_roundedBundleTypeOfBundle] using
+        exact
           hcount
       _ = supply k :=
         paper_lmms_theorem_3_3_roundedGoodsSupplyOfSupply_eq supply k
@@ -17275,12 +17256,12 @@
     have hwindow_imin_item :
         Theorem34.boundedAroundAverage LR
           (Theorem34.commonLoad itemValue (B imin)) := by
-      simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+      exact
         hB_window imin
     have hwindow_imax_item :
         Theorem34.boundedAroundAverage LR
           (Theorem34.commonLoad itemValue (B imax)) := by
-      simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+      exact
         hB_window imax
     have hpair_load :
         (Theorem33.roundedBundleTypeLoad L (typeOf imin),
@@ -17305,7 +17286,7 @@
   refine ⟨B, hB_alloc, hB_nonempty, hB_opt, ?_, p, typeOf, hpair, htypes,
     hcounts, search, hsearch⟩
   intro i
-  simpa [itemValue, paper_lmms_theorem_3_3_roundedSupplyValue] using
+  exact
     hB_window i
 
 /--
@@ -35148,7 +35129,7 @@
           (highGoods := highGoods) (lowGoods := lowGoods)
           (sourceValue := sourceValue) indexOf)
         rounded typeOf htypes hcounts
-    simpa [paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue] using h
+    exact h
   have hsource_to_rounded :=
     le_trans hrounded_to_chosen hchosen_forward
   rcases
@@ -35450,7 +35431,7 @@
           (highGoods := highGoods) (lowGoods := lowGoods)
           (sourceValue := sourceValue) indexOf)
         rounded typeOf htypes hcounts
-    simpa [paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue] using h
+    exact h
   have hsource_to_rounded :=
     le_trans hrounded_to_chosen hchosen_forward
   refine
```
