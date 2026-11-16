# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

The following exact diffs retain the recorded compatibility choices. Source hash and import-relocation checks do not prove global equivalence of the historical and modern library environments.

## AppliedModelingLib/Foundations/Math/FiniteSum.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Math/FiniteSum.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Math/FiniteSum.lean
@@ -1,3 +1,4 @@
+import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
 import Mathlib.Algebra.BigOperators.Group.Finset.Basic
 import Mathlib.Algebra.BigOperators.Group.List.Basic
 import Mathlib.Algebra.BigOperators.Fin
@@ -394,13 +395,13 @@
     exact Finset.prod_pos hlow_failure_pos
   have hlowProd_le_one : lowProd ≤ 1 := by
     dsimp [lowProd]
-    exact Finset.prod_le_one hlow_nonneg hlow_failure_le_one
+    exact Finset.prod_le_one₀ hlow_nonneg hlow_failure_le_one
   have hfloor_le_ratioProd : globalFloor ≤ ratioProd := by
     calc
       globalFloor ≤ ∏ i ∈ s, ratioFloor i := hprod_floor
       _ ≤ ratioProd := by
         dsimp [ratioProd]
-        exact Finset.prod_le_prod hratio_nonneg hratio
+        exact Finset.prod_le_prod₀ hratio_nonneg hratio
   have hratioProd_eq : ratioProd = highProd / lowProd := by
     dsimp [ratioProd, highProd, lowProd]
     exact Finset.prod_div_distrib (s := s)
```

## AppliedModelingLib/Foundations/Math/FiniteOptimization.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Math/FiniteOptimization.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Math/FiniteOptimization.lean
@@ -76,10 +76,8 @@
     IsClosed {mass : α → ℝ | FiniteProbabilitySimplex mass} := by
   have hnonneg :
       IsClosed {mass : α → ℝ | ∀ i : α, 0 ≤ mass i} := by
-    simpa [Set.setOf_forall] using
-      (isClosed_iInter fun i : α =>
-        (isClosed_Ici.preimage (continuous_apply i) :
-          IsClosed {mass : α → ℝ | mass i ∈ Set.Ici (0 : ℝ)}))
+    simp only [Set.setOf_forall]
+    exact isClosed_iInter (fun i : α => isClosed_le continuous_const (continuous_apply i))
   have hsum_cont : Continuous (fun mass : α → ℝ => ∑ i : α, mass i) :=
     continuous_finset_sum _ fun i _hi => continuous_apply i
   have hsum :
```

## AppliedModelingLib/Foundations/Probability/FiniteExpectation.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/FiniteExpectation.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/FiniteExpectation.lean
@@ -361,10 +361,10 @@
           exact (pmfExp_pmfProduct_equiv (optionFinEquivFinSucc n) μ F).symm
     _ = pmfPairExp (pmfProduct (Fin n) α μ) μ
         (fun history fresh => F (extendFinDraw n history fresh)) := by
-          simpa [extendFinDraw] using
-            (pmfExp_pmfProduct_option_eq_pairExp μ
+          unfold extendFinDraw
+          convert! (pmfExp_pmfProduct_option_eq_pairExp μ
               (fun sample => F (fun index =>
-                sample ((optionFinEquivFinSucc n).symm index))))
+                sample ((optionFinEquivFinSucc n).symm index)))) using 1 <;> rfl
 
 /--
 Flattening a finite two-level iid sample preserves finite expectations of
@@ -602,8 +602,7 @@
   calc
     pmfExp (pmfProduct ι α μ) (fun sample => F (sample i)) =
         pmfExp (pmfProduct (Option rest) α μ) (fun sample => F (sample none)) := by
-      simpa [e] using
-        (pmfExp_pmfProduct_equiv e μ (fun sample : Option rest → α => F (sample none)))
+      convert! (pmfExp_pmfProduct_equiv e μ (fun sample : Option rest → α => F (sample none))) using 1 <;> rfl
     _ = pmfPairExp (pmfProduct rest α μ) μ
         (fun sample newItem => F ((extendDraw sample newItem) none)) := by
       exact pmfExp_pmfProduct_option_eq_pairExp μ (fun sample => F (sample none))
```

## AppliedModelingLib/Applications/RecommenderSystems/Allocation.lean

```diff
--- upstream/AppliedModelingLib/Applications/RecommenderSystems/Allocation.lean
+++ lean-4.34.1/AppliedModelingLib/Applications/RecommenderSystems/Allocation.lean
@@ -1077,7 +1077,7 @@
           rw [htotal] at hle
           exact hle)⟩,
     by
-      simpa [HasTotal] using hfeas⟩
+      simpa [HasTotal, total] using hfeas⟩
 
 @[simp] theorem toAllocation_ofHasTotal {N : ℕ}
     (a : Allocation κ) (hfeas : HasTotal a N) :
```

## AppliedModelingLib/Foundations/Math/ExponentialBounds.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Math/ExponentialBounds.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Math/ExponentialBounds.lean
@@ -1537,7 +1537,7 @@
     exact neg_lt_zero.mpr (mul_pos hy₀ hr_minus_one_pos)
   have hratio : Real.exp (-(y * (r - 1))) ≤ q := by
     apply Real.exp_le_exp.mpr
-    dsimp [q]
+    try dsimp [q]
     have hscaled := mul_le_mul_of_nonneg_right hy hr_minus_one_pos.le
     linarith
   have hright : Summable (fun n : ℕ => Real.exp (-y) * q ^ n) := by
```

## AppliedModelingLib/Foundations/Math/Asymptotics.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Math/Asymptotics.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Math/Asymptotics.lean
@@ -1452,7 +1452,7 @@
       Tendsto
         (fun N : ℕ => Real.log (1 - (1 : ℝ) / (((N + 1 : ℕ) : ℝ))))
         atTop (nhds 0) := by
-    simpa [Real.log_one] using
+    simpa only [Function.comp_def, Real.log_one] using
       (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
   simpa using hlog.neg
 
@@ -1840,7 +1840,7 @@
     Tendsto (fun N : ℕ =>
       ((Nat.ceil (a * ((N + 1 : ℕ) : ℝ)) : ℝ) / ((N + 1 : ℕ) : ℝ)))
       atTop (nhds a) := by
-  simpa using
+  simpa only [Function.comp_def] using
     (tendsto_nat_ceil_mul_div_atTop ha).comp tendsto_nat_succ_cast_atTop
 
 /--
```

## PRPKG24AccuracyDiversity/Examples.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/Examples.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/Examples.lean
@@ -168,7 +168,7 @@
   have h := B.forwardMarginal_le_backwardMarginal_of_optimum
     (N := N) (a := twoTypeAllocation a b)
     (src := (0 : ItemType 2)) (dst := (1 : ItemType 2)) hopt (by decide)
-    (by simpa using ha)
+    (by simpa [AppliedModelingLib.Allocation.CanMoveOne] using ha)
   simpa using h
 
 /--
@@ -184,7 +184,7 @@
   have h := B.forwardMarginal_le_backwardMarginal_of_optimum
     (N := N) (a := twoTypeAllocation a b)
     (src := (1 : ItemType 2)) (dst := (0 : ItemType 2)) hopt (by decide)
-    (by simpa using hb)
+    (by simpa [AppliedModelingLib.Allocation.CanMoveOne] using hb)
   simpa using h
 
 /--
@@ -347,7 +347,7 @@
     (hprob_pos : 0 < B.successProb 0)
     (hprob_lt_one : B.successProb 0 < 1) :
     equalTwoTypeProfile.Approx (twoTypeAllocation a b) (1 / (N : ℝ)) := by
-  have hsum : a + b = N := by simpa using hopt.1
+  have hsum : a + b = N := by simpa [ConsumptionModel.FeasibleAtTotal, AppliedModelingLib.Allocation.HasTotal] using hopt.1
   have hpos : 0 < a + b := by simpa [hsum] using hNpos
   have hbal :=
     twoTypeAllocation_balanced_of_symmetric_bernoulli_optimum
```

## AppliedModelingLib/Foundations/Math/AbsolutelyContinuous.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Math/AbsolutelyContinuous.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Math/AbsolutelyContinuous.lean
@@ -140,8 +140,8 @@
     have hdderiv : ∀ x ∈ Set.Ioo a y, HasDerivAt d 0 x := by
       intro x hx
       have hxab : x ∈ Set.Ioo a b := ⟨hx.1, hx.2.trans_le hy.2⟩
-      simpa only [d, sub_self] using
-        (hfderiv x hxab).sub (hgderiv x hxab)
+      unfold d
+      convert! (hfderiv x hxab).sub (hgderiv x hxab) using 1 <;> simp
     obtain ⟨c, hc, hcSlope⟩ :=
       exists_hasDerivAt_eq_slope d (fun _ => 0) hay hdcont hdderiv
     have hya_ne : y - a ≠ 0 := sub_ne_zero.mpr hay.ne'
@@ -215,7 +215,7 @@
       simpa using
         (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
   | succ n hn =>
-      simpa [pow_succ] using hn.mul hAC
+      convert! hn.mul hAC using 1 <;> simp [pow_succ]
 
 end RealAnalysis
 end AppliedModelingLib
```

## AppliedModelingLib/Foundations/Math/EpsilonContinuity.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Math/EpsilonContinuity.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Math/EpsilonContinuity.lean
@@ -21,7 +21,7 @@
     (hf : ContinuousAt f x) :
     EpsilonContinuousAt f x := by
   rw [Metric.continuousAt_iff] at hf
-  simpa [Real.dist_eq] using hf
+  simpa [EpsilonContinuousAt, Real.dist_eq] using hf
 
 /--
 Composing an epsilon-delta continuous real function with a mathlib-continuous
@@ -75,7 +75,7 @@
       have hs_cont :
           ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
         exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
-      simpa [Finset.sum_insert, ha] using ha_cont.add hs_cont
+      convert! ha_cont.add hs_cont using 1 <;> simp [Finset.sum_insert, ha] <;> rfl
 
 /-- Sums of epsilon-delta continuous real functions are continuous. -/
 theorem epsilonContinuousAt_add {f g : ℝ → ℝ} {x : ℝ}
```

## AppliedModelingLib/Foundations/Probability/RealDistribution.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/RealDistribution.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/RealDistribution.lean
@@ -1,3 +1,5 @@
+import Mathlib.Analysis.Calculus.Deriv.MeanValue
+import Mathlib.Analysis.Calculus.ContDiff.Deriv
 import AppliedModelingLib.Foundations.Math.FiniteSum
 import AppliedModelingLib.Foundations.Math.ConnectedCovers
 import AppliedModelingLib.Foundations.Math.OrderedPairs
@@ -53,7 +55,7 @@
     lowerCDFMass (Measure.map (fun r : ℝ => r * c) μ) z =
       lowerCDFMass μ (z / c) := by
   letI : IsProbabilityMeasure (Measure.map (fun r : ℝ => r * c) μ) :=
-    Measure.isProbabilityMeasure_map (measurable_id.mul measurable_const).aemeasurable
+    (by infer_instance)
   unfold lowerCDFMass
   have hmeas : Measurable (fun r : ℝ => r * c) := measurable_id.mul measurable_const
   rw [map_measureReal_apply hmeas measurableSet_Iic]
@@ -132,7 +134,7 @@
     funext z
     exact lowerCDFMass_map_mul_const μ hc
   rw [hfun]
-  simpa only [Function.comp_apply] using hcomp
+  convert! hcomp using 1 <;> rfl
 
 /-- Multiplying a measure by a nonzero `ENNReal` scalar does not change its
 topological support. -/
@@ -359,7 +361,7 @@
 -/
 theorem lowerCDFMass_map_fst_eq_map_snd_of_ordered_support
     {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
-    [NoAtoms (Measure.map Prod.fst ν)] [NoAtoms (Measure.map Prod.snd ν)]
+    [NullSingletonClass (Measure.map Prod.fst ν)] [NullSingletonClass (Measure.map Prod.snd ν)]
     (hordered : ∀ p ∈ ν.support, ∀ q ∈ ν.support,
       p.1 < q.1 → p.2 ≤ q.2)
     {z : ℝ × ℝ} (hz : z ∈ ν.support) :
@@ -1754,7 +1756,7 @@
 the CDF jump even when `(a,b)` is disjoint from the topological support.
 -/
 theorem lowerCDFMass_eq_of_Ioo_subset_compl_support_of_noAtoms
-    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] {a b : ℝ}
+    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] {a b : ℝ}
     (hab : a ≤ b) (hgap : Set.Ioo a b ⊆ μ.supportᶜ) :
     lowerCDFMass μ a = lowerCDFMass μ b := by
   have hsupport_zero : μ μ.supportᶜ = 0 := by
@@ -1784,7 +1786,7 @@
 model boundary.
 -/
 theorem lowerCDFMass_eq_zero_of_forall_mem_support_le
-    (μ : Measure ℝ) [NoAtoms μ] {a : ℝ}
+    (μ : Measure ℝ) [NullSingletonClass μ] {a : ℝ}
     (hmin : ∀ x ∈ μ.support, a ≤ x) :
     lowerCDFMass μ a = 0 := by
   have hsupport_zero : μ μ.supportᶜ = 0 := by
@@ -1926,7 +1928,7 @@
         (by
           refine ⟨a + 1, by linarith, ?_⟩
           exact measure_ne_top μ (Ioc a (a + 1)))
-    simpa [h_inter_empty] using h
+    simpa only [h_inter_empty, Measure.real, Function.comp_def, measure_empty] using h
   have hreal :
       Tendsto (fun b => (μ (Ioc a b)).toReal) (𝓝[>] a) (𝓝 0) :=
     (ENNReal.tendsto_toReal (by simp)).comp hmeasure
```

## AppliedModelingLib/Foundations/Probability/OrderStatistics.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/OrderStatistics.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/OrderStatistics.lean
@@ -1155,8 +1155,8 @@
 
 theorem ascendingOrderStatistic_mono {n : ℕ} (sample : Fin n → ℝ) :
     Monotone (ascendingOrderStatistic sample) := by
-  simpa [ascendingOrderStatistic, Function.comp_def] using
-    Tuple.monotone_sort sample
+  unfold ascendingOrderStatistic
+  convert! Tuple.monotone_sort sample using 1 <;> rfl
 
 theorem ascendingOrderStatistic_filter_card_eq
     {n : ℕ} (sample : Fin n → ℝ) (x : ℝ) :
@@ -1511,7 +1511,7 @@
 support endpoint is compared with the zero action.
 -/
 theorem iidMaximumCdf_eq_zero_of_forall_mem_support_le
-    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
+    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
     (hn : n ≠ 0) {a : ℝ}
     (hmin : ∀ x ∈ μ.support, a ≤ x) :
     iidMaximumCdf (n := n) μ a = 0 := by
@@ -1532,7 +1532,7 @@
     iidMaximumCdf (n := n) (Measure.map g μ) (g x) =
       iidMaximumCdf (n := n) μ x := by
   letI : IsProbabilityMeasure (Measure.map g μ) :=
-    Measure.isProbabilityMeasure_map hg.aemeasurable
+    (by infer_instance)
   rw [iidMaximumCdf_eq_lowerCDFMass_pow,
     iidMaximumCdf_eq_lowerCDFMass_pow,
     lowerCDFMass_map_eq_of_support_strictMonoOn hg hstrict hx]
@@ -1554,7 +1554,7 @@
     iidMaximumCdf (n := n) (Measure.map Prod.snd ν) (g x) =
       iidMaximumCdf (n := n) (Measure.map Prod.fst ν) x := by
   letI : IsProbabilityMeasure (Measure.map Prod.fst ν) :=
-    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
+    (by infer_instance)
   rw [map_snd_eq_map_graph_map_fst_of_support_graph hg hgraph]
   exact iidMaximumCdf_map_eq_of_support_strictMonoOn
     (Measure.map Prod.fst ν) hg hstrict hx
@@ -1566,7 +1566,7 @@
 atom by default.
 -/
 theorem iidMaximumCdf_eq_of_Ioo_subset_compl_support_of_noAtoms
-    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
+    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
     {a b : ℝ} (hab : a ≤ b) (hgap : Set.Ioo a b ⊆ μ.supportᶜ) :
     iidMaximumCdf (n := n) μ a = iidMaximumCdf (n := n) μ b :=
   iidMaximumCdf_eq_of_lowerCDFMass_eq μ
@@ -1834,9 +1834,8 @@
 
 theorem reflectedSample_measurable (M : ℝ) {n : ℕ} :
     Measurable (fun sample : Fin n → ℝ => reflectedSample M sample) := by
-  refine measurable_pi_lambda _ ?_
-  intro i
-  exact measurable_const.sub (measurable_pi_apply i)
+  unfold reflectedSample
+  exact measurable_pi_iff.mpr (fun i => measurable_const.sub (measurable_pi_apply i))
 
 theorem reflectedAscendingOrderStatistic_measurable
     (M : ℝ) {n : ℕ} (rank : Fin n) :
@@ -1863,7 +1862,7 @@
       simp only [Fin.val_rev]
       omega
     have hsort := ascendingOrderStatistic_mono sample hrev
-    dsimp [ascendingOrderStatistic, reflectedSample, Function.comp_def, σ] at hsort ⊢
+    dsimp [ascendingOrderStatistic, reflectedSample, Function.comp_def, σ, Fin.revPerm] at hsort ⊢
     linarith
   have hsorted :
       (reflectedSample M sample) ∘ σ =
@@ -3147,7 +3146,8 @@
     fun sample x => reflectedBottomKRankCountLayer M k sample x
   have h_layer_integrable' :
       MeasureTheory.Integrable (Function.uncurry f) (μ.prod ν) := by
-    simpa [ν, f, Function.uncurry] using h_layer_integrable
+    unfold ν f
+    convert! h_layer_integrable using 1 <;> rfl
   have hpoint :
       (fun sample : Fin n → ℝ => reflectedBottomKSum M sample k) =ᵐ[μ]
         fun sample : Fin n → ℝ => ∫ x, f sample x ∂ν := by
@@ -3583,7 +3583,7 @@
     orderStatisticTopKSumFromMean
         (expectedOrderStatisticMeanSeq sampleMeasure) k a =
       expectedSampleTopKSum (sampleMeasure a) k := by
-  simpa [expectedOrderStatisticMeanSeq] using
+  simpa [orderStatisticTopKSumFromMean, expectedSampleOrderStatisticMean, expectedOrderStatisticMeanSeq, orderStatisticTopKSumFromMean, expectedSampleOrderStatisticMean] using
     expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
       (sampleMeasure a) k h_integrable
 
@@ -3608,7 +3608,7 @@
         orderStatisticTopKSumFromMean
           (expectedOrderStatisticMeanSeq sampleMeasure) k a =
       expectedReflectedBottomKSum M (sampleMeasure a) k := by
-  simpa [expectedOrderStatisticMeanSeq] using
+  simpa [orderStatisticTopKSumFromMean, expectedSampleOrderStatisticMean, expectedOrderStatisticMeanSeq, orderStatisticTopKSumFromMean, expectedSampleOrderStatisticMean] using
     expectedSampleOrderStatisticTopKEndpointLoss_eq_expectedReflectedBottomKSum
       M (sampleMeasure a) k h_order_integrable h_top_integrable
```

## AppliedModelingLib/Foundations/Math/BinomialBounds.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Math/BinomialBounds.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Math/BinomialBounds.lean
@@ -145,7 +145,7 @@
     simpa [hprod]
   exact
     Nat.twoStepInduction
-      (P := fun m : ℕ =>
+      (motive := fun m : ℕ =>
         c * s ^ m ≤ pUp ^ (m / 2) * pDown ^ (m - m / 2))
       hbase0 hbase1
       (fun k hk _hk1 => by
```

## PRPKG24AccuracyDiversity/Uniform.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/Uniform.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/Uniform.lean
@@ -129,9 +129,7 @@
 instance boundedReflectedPowerSourceMeasure_isProbabilityMeasure (beta : ℝ) :
     IsProbabilityMeasure (boundedReflectedPowerSourceMeasure beta) := by
   unfold boundedReflectedPowerSourceMeasure
-  exact Measure.isProbabilityMeasure_map
-    ((by
-      fun_prop : Measurable (fun u : ℝ => 1 - u ^ (1 / beta))).aemeasurable)
+  infer_instance
 
 theorem boundedReflectedPowerSourceMeasure_ae_bounds {beta : ℝ}
     (hbeta_pos : 0 < beta) :
@@ -895,7 +893,7 @@
         AppliedModelingLib.Probability.expectedUpperOrderStatistic
           (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure))
           ⟨r, hrq⟩ := by
-          simpa [uniform01IidOrderStatisticMeanSeq, expectedOrderStatisticMeanSeq] using
+          simpa [uniform01IidOrderStatisticMeanSeq, expectedOrderStatisticMeanSeq, AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq] using
             AppliedModelingLib.Probability.expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
               (μ := MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure))
               (a := q) (r := r) hrq
```

## PRPKG24AccuracyDiversity/TailHomogeneity.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/TailHomogeneity.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/TailHomogeneity.lean
@@ -286,8 +286,7 @@
     (likelihood perItemValue : ItemType T → ℝ) (a : CountAllocation T) :
     (ConsumptionModel.linearized likelihood perItemValue).objective a =
       ∑ t : ItemType T, (a.count t : ℝ) * (likelihood t * perItemValue t) := by
-  simpa [ConsumptionModel.objective, ConsumptionModel.linearized,
-    ConsumptionModel.linearValueOfCount] using
+  exact
     AppliedModelingLib.Allocation.objective_linearValueOfCount_eq_sum_count_mul_score
       likelihood perItemValue a
 
@@ -301,9 +300,7 @@
       ∀ t, likelihood t * perItemValue t ≤ likelihood best * perItemValue best) :
     (ConsumptionModel.linearized likelihood perItemValue).IsOptimalAtTotal
       N (allOnTypeAllocation N best) := by
-  simpa [ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
-    ConsumptionModel.objective, ConsumptionModel.linearized,
-    ConsumptionModel.linearValueOfCount, allOnTypeAllocation] using
+  exact
     AppliedModelingLib.Allocation.allOnTypeAllocation_isOptimalAtTotal_linearValueOfCount
       likelihood perItemValue N best hbest
 
@@ -326,9 +323,7 @@
       (weight := likelihood) (perUnitValue := perItemValue) (N := N) (a := a)
       (k := t) (best := best)
       (by
-        simpa [ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
-          ConsumptionModel.objective, ConsumptionModel.linearized,
-          ConsumptionModel.linearValueOfCount] using hopt)
+        exact hopt)
       hstrict
 
 /--
```

## AppliedModelingLib/Foundations/Math/PowerComparisons.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Math/PowerComparisons.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Math/PowerComparisons.lean
@@ -1,3 +1,4 @@
+import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
 import AppliedModelingLib.Foundations.Math.Asymptotics
 import Mathlib.Analysis.SpecialFunctions.Pow.Real
 import Mathlib.Tactic
```

## PRPKG24AccuracyDiversity/SeparableAsymptotic.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/SeparableAsymptotic.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/SeparableAsymptotic.lean
@@ -976,7 +976,7 @@
         unfold ConsumptionModel.weightedBackwardMarginal
           TopKValueOracle.toConsumptionModel
         rw [dif_neg (Nat.ne_of_gt hqpos)]]
-    simpa [TopKValueOracle.toConsumptionModel,
+    simpa [M, TopKValueOracle.toConsumptionModel,
       ConsumptionModel.weightedForwardMarginal,
       ConsumptionModel.marginalValue, TopKValueOracle.marginalTopK,
       AppliedModelingLib.Allocation.marginal] using hltq
@@ -1499,7 +1499,8 @@
             (topKPowerLawAsymptoticDstPerturbation_tends_to_zero
               C likelihood γ hlike_pos t))
     simpa using hsum
-  simpa [topKPowerLawAsymptoticFOCError] using
+  unfold topKPowerLawAsymptoticFOCError
+  simpa using
     (AppliedModelingLib.Math.invSqrtSuccError_tendsToZero.add
       (hsrc.const_mul 2)).add (hdst.const_mul 2)
```

## PRPKG24AccuracyDiversity/Bounded.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/Bounded.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/Bounded.lean
@@ -82,7 +82,7 @@
   convert
     (tendsto_rpow_neg_atTop hη_pos).comp
       (tendsto_natCast_atTop_atTop.comp
-        (Filter.tendsto_add_atTop_nat 1)) using 1
+        (Filter.tendsto_add_atTop_nat 1)) using 1 <;> rfl
 
 theorem boundedPowerMarginalScale_one_eq_inv_sq (q : ℕ) :
     boundedPowerMarginalScale 1 q =
@@ -120,7 +120,7 @@
     have h :=
       hratio.rpow_const (p := eta)
         (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
-    simpa using h
+    convert! h using 1 <;> simp <;> rfl
   refine Tendsto.congr' ?_ hrpow
   filter_upwards with q
   have hq1_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
@@ -264,7 +264,7 @@
     Tendsto (boundedTailScale beta) atTop (nhds 0) := by
   have hexp_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
   change Tendsto (fun a : ℕ => ((a : ℝ) ^ (-(1 / beta)))) atTop (nhds 0)
-  simpa [one_div] using
+  simpa only [one_div, Function.comp_def] using
     (tendsto_rpow_neg_atTop hexp_pos).comp
       tendsto_natCast_atTop_atTop
 
@@ -326,7 +326,7 @@
     have h :=
       hratio.rpow_const (p := 1 / beta)
         (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
-    simpa using h
+    convert! h using 1 <;> simp <;> rfl
   refine Tendsto.congr' ?_ hrpow
   filter_upwards
     [boundedTailScale_div_succ_ratio_eventually_eq_rpow hbeta_pos] with q hq
@@ -542,10 +542,7 @@
       (TopKValueOracle.ofOrderStatisticMean T μ) k
       (boundedPowerMarginalScale beta)
       (fun _ : ItemType T => limitCoeff) := by
-  simpa [topKExpectationOracleOfTopKValueOracle,
-      AppliedModelingLib.Probability.TopKExpectationOracle.orderStatisticTopKExpectationOracle,
-      TopKValueOracle.ofOrderStatisticMean]
-    using
+  exact
       C.toOrderStatisticScaledMarginalCertificate
         |>.toTopKExpectationScaledMarginalLimitCertificate (ItemType T)
 
@@ -1696,7 +1693,7 @@
     have hpow :
         Filter.Tendsto (fun q : ℕ => ((q : ℝ) ^ (-η)))
           Filter.atTop (nhds 0) := by
-      simpa using
+      simpa only [Function.comp_def] using
         (tendsto_rpow_neg_atTop hη_pos).comp
           tendsto_natCast_atTop_atTop
     simpa using hpow.const_mul C
@@ -1763,12 +1760,12 @@
       hη_pos hγ_eq hcoeff_pos (le_of_lt hη_pos) hk hlike_pos
       (by
         intro src qsrc hsrc_floor
-        simpa [η] using
+        exact
           boundedReflectedPowerOrderStatistic_weightedBackwardMarginal_le_power_bound
             likelihood hbeta_pos hk hlike_pos hsrc_floor src)
       (by
         intro dst qdst hdst_floor
-        simpa [η] using
+        exact
           boundedReflectedPowerOrderStatistic_power_bound_le_weightedForwardMarginal
             likelihood hbeta_pos hk hlike_pos (le_of_lt hdst_floor) dst)
 
@@ -2548,7 +2545,7 @@
     have h :=
       (bounded_one_sub_div_pow_tendsto_exp z).div hdenom
         (by norm_num : (1 : ℝ) ≠ 0)
-    simpa using h
+    convert! h using 1 <;> simp <;> rfl
   refine Tendsto.congr' ?_ hquot
   filter_upwards
     [eventually_ge_atTop j,
@@ -2612,7 +2609,7 @@
     have h :=
       (bounded_one_sub_of_nat_mul_tendsto_pow_tendsto_exp hu).div hdenom
         (by norm_num : (1 : ℝ) ≠ 0)
-    simpa using h
+    convert! h using 1 <;> simp <;> rfl
   refine Tendsto.congr' ?_ hquot
   filter_upwards
     [eventually_ge_atTop j,
@@ -6959,7 +6956,7 @@
   k_pos := C.k_pos
   term_asymptotic := by
     intro p
-    simpa [boundedLemmaD2IndexedIntegralTerm] using
+    exact
       (C.fixed p).integralTerm_asymptoticEquivalent
 
 end BoundedLemmaD2SplitIntegralFiniteCertificate
@@ -7087,7 +7084,7 @@
   k_pos := C.k_pos
   term_asymptotic := by
     intro p
-    simpa [boundedLemmaD2IndexedIntegralTerm] using
+    exact
       (C.fixedCertificate p).integralTerm_asymptoticEquivalent
 
 end BoundedLemmaD2DominatedIntegralAsymptoticCertificate
@@ -7215,7 +7212,7 @@
    boundedLemmaD2_reflected_source_loss_asymptoticEquivalent
     sourceMean (boundedLemmaD2IndexedIntegralTerm G)
     (fun a i => by
-      simpa [boundedLemmaD2IndexedIntegralTerm] using hsource a i)
+      exact hsource a i)
     C
 
 /--
```

## AppliedModelingLib/Foundations/Probability/Pareto.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/Pareto.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/Pareto.lean
@@ -596,7 +596,7 @@
     AppliedModelingLib.Math.integrableOn_Ioo_zero_one_rpow_mul_one_sub_rpow ha hb
   have hg :
       IntegrableOn g (Set.Ioo (0 : ℝ) 1) := by
-    simpa [g, mul_assoc] using hbeta_int.const_mul (1 / α)
+    simpa [g, mul_assoc, IntegrableOn] using hbeta_int.const_mul (1 / α)
   have hg_image :
       IntegrableOn g
         ((fun x : ℝ => x ^ (-α)) '' Set.Ioi (1 : ℝ)) := by
```

## PRPKG24AccuracyDiversity/Pareto.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/Pareto.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/Pareto.lean
@@ -1118,7 +1118,7 @@
         =
           AppliedModelingLib.Probability.expectedUpperOrderStatistic
             (paretoIidSampleMeasure α q) ⟨r, hrq⟩ := by
-          simpa [expectedOrderStatisticMeanSeq] using
+          simpa [expectedOrderStatisticMeanSeq, AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq] using
             AppliedModelingLib.Probability.expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
               (μ := paretoIidSampleMeasure α q) (r := r) (a := q) hrq
     _ = paretoRankGammaRatioMean α r q := by
@@ -1590,10 +1590,7 @@
       (TopKValueOracle.ofOrderStatisticMean T μ) k
       (paretoPowerMarginalScale α)
       (fun _ : ItemType T => limitCoeff) := by
-  simpa [topKExpectationOracleOfTopKValueOracle,
-      AppliedModelingLib.Probability.TopKExpectationOracle.orderStatisticTopKExpectationOracle,
-      TopKValueOracle.ofOrderStatisticMean]
-    using
+  exact
       C.toOrderStatisticScaledMarginalCertificate
         |>.toTopKExpectationScaledMarginalLimitCertificate (ItemType T)
 
@@ -1653,7 +1650,7 @@
           =
             AppliedModelingLib.Probability.expectedUpperOrderStatistic
               (paretoIidSampleMeasure α 1) ⟨0, by norm_num⟩ := by
-            simpa [paretoIidOrderStatisticMeanSeq] using
+            simpa [paretoIidOrderStatisticMeanSeq, expectedOrderStatisticMeanSeq, AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq] using
               AppliedModelingLib.Probability.expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
                 (μ := paretoIidSampleMeasure α 1) (r := 0) (a := 1)
                 (by norm_num)
@@ -1855,12 +1852,12 @@
       hη_pos hγ_eq hcoeff_pos (by norm_num) hk hlike_pos
       (by
         intro src qsrc hsrc_floor
-        simpa [η] using
+        exact
           paretoIidOrderStatistic_weightedBackwardMarginal_le_power_bound
             likelihood hα hk hlike_pos hsrc_floor src)
       (by
         intro dst qdst hdst_floor
-        simpa [η, Nat.cast_add, Nat.cast_one, add_assoc] using
+        simpa [η, Nat.cast_add, Nat.cast_one, add_assoc, ConsumptionModel.weightedForwardMarginal, paretoIidOrderStatisticConsumptionModel, TopKValueOracle.toConsumptionModel] using
           paretoIidOrderStatistic_power_bound_le_weightedForwardMarginal
             likelihood hα hk hlike_pos (le_of_lt hdst_floor) dst)
```

## AppliedModelingLib/Foundations/Probability/Exponential.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/Exponential.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/Exponential.lean
@@ -297,7 +297,7 @@
 theorem ae_nonnegative (M : Model) :
     (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[M.measure] (fun x : ℝ => x) := by
   rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
-  simpa [Set.compl_setOf] using M.measure_Iio_zero
+  simpa only [not_le, Set.Iio] using M.measure_Iio_zero
 
 /-- Real-valued PDF of the positive-rate exponential model. -/
 noncomputable def pdfReal (M : Model) (x : ℝ) : ℝ :=
@@ -722,6 +722,7 @@
   exact
     (exp_neg_integrableOn_Ioi (0 : ℝ) hnrate_pos).congr_fun
       (fun x _hx => by
+        dsimp only
         rw [show -((n : ℝ) * rate) * x =
             -(((n : ℝ) * rate) * x) by ring]
         exact (exp_neg_mul_pow_nat rate x n).symm)
@@ -1090,8 +1091,7 @@
     M.isProbabilityMeasure_iidProductMeasure q
   have h_nonneg :
       (fun _ : Fin q → ℝ => (0 : ℝ)) ≤ᵐ[μ] (finiteSampleMax (q := q)) := by
-    simpa [μ] using
-      M.iidProductMeasure_finiteSampleMax_nonnegative_ae (q := q)
+    exact M.iidProductMeasure_finiteSampleMax_nonnegative_ae (q := q)
   have h_layer :=
     MeasureTheory.lintegral_eq_lintegral_meas_lt (μ := μ)
       h_nonneg finiteSampleMax_measurable.aemeasurable
```

## PRPKG24AccuracyDiversity/ExponentialTopOne.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/ExponentialTopOne.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/ExponentialTopOne.lean
@@ -1772,7 +1772,7 @@
         MeasureTheory.Integrable
           (fun x : ℝ => e x ^ (q - m))
           (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
-      simpa [e] using
+      simpa [e, MeasureTheory.IntegrableOn] using
         AppliedModelingLib.Probability.Exponential.integrableOn_exp_neg_mul_pow_Ioi
           lambda hlambda_pos hqm_pos
     have hterm :
@@ -2082,7 +2082,7 @@
         MeasureTheory.Integrable
           (fun x : ℝ => e x ^ (q - m))
           (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
-      simpa [e] using
+      simpa [e, MeasureTheory.IntegrableOn] using
         AppliedModelingLib.Probability.Exponential.integrableOn_exp_neg_mul_pow_Ioi
           lambda hlambda_pos hqm_pos
     exact hbase.const_mul _
@@ -2887,7 +2887,7 @@
         (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
   have hf_int :
       MeasureTheory.Integrable (Function.uncurry f) (μ.prod ν) := by
-    simpa [M, μ, ν, f, Function.uncurry] using
+    exact
       thresholdMinSuccessCount_prod_integrable lambda hlambda_pos (q := q) k
   simpa [M, μ, ν, f] using
     (MeasureTheory.integral_integral_swap (μ := μ) (ν := ν) (f := f) hf_int)
```

## PRPKG24AccuracyDiversity/DecayingBernoulli.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/DecayingBernoulli.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/DecayingBernoulli.lean
@@ -1,3 +1,4 @@
+import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
 import PRPKG24AccuracyDiversity.SeparableAsymptotic
 import PRPKG24AccuracyDiversity.Exchange
 import PRPKG24AccuracyDiversity.Bernoulli
@@ -98,7 +99,7 @@
   calc
     ∏ i ∈ s, (1 - success i)
         ≤ ∏ i ∈ s, Real.exp (-(success i)) :=
-          Finset.prod_le_prod
+          Finset.prod_le_prod₀
             (fun i _ => sub_nonneg.mpr (hs_le_one i))
             (fun i _ => Real.one_sub_le_exp_neg (success i))
     _ = Real.exp (∑ i ∈ s, -(success i)) := by
@@ -189,7 +190,7 @@
   have hprod_factor_le :
       ∏ i ∈ Finset.Ico q r, (1 - success i)⁻¹ ≤
         ∏ i ∈ Finset.Ico q r, Real.exp (2 * success i) :=
-    Finset.prod_le_prod hfactor_nonneg hfactor_le
+    Finset.prod_le_prod₀ hfactor_nonneg hfactor_le
   have hprod_inv :
       (∏ i ∈ Finset.Ico q r, (1 - success i))⁻¹ =
         ∏ i ∈ Finset.Ico q r, (1 - success i)⁻¹ := by
@@ -1286,7 +1287,7 @@
   have hprod_factor_le :
       ∏ i ∈ Finset.Ico q r, (1 - success i)⁻¹ ≤
         ∏ i ∈ Finset.Ico q r, ratio i ^ c * Real.exp (corr i) :=
-    Finset.prod_le_prod hfactor_nonneg hfactor_le
+    Finset.prod_le_prod₀ hfactor_nonneg hfactor_le
   have hprod_inv :
       (∏ i ∈ Finset.Ico q r, (1 - success i))⁻¹ =
         ∏ i ∈ Finset.Ico q r, (1 - success i)⁻¹ := by
```

## AppliedModelingLib/Foundations/Probability/FiniteSupportMGF.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/FiniteSupportMGF.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/FiniteSupportMGF.lean
@@ -483,8 +483,7 @@
               (fun a =>
                 (μ a).toReal * (score a * Real.exp (zNeg * score a))) := by
       dsimp [g]
-      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (i := aNeg) hmem]
-      rw [Finset.sdiff_singleton_eq_erase]
+      exact (Finset.add_sum_erase _ _ hmem).symm
     rw [hsum_eq]
     linarith
   have hzero_mem : (0 : ℝ) ∈ Set.Icc (g zNeg) (g 0) :=
@@ -967,7 +966,7 @@
   rw [hfun]
   have hlinear : HasDerivAt (fun z : ℝ => z * a) a z0 := by
     simpa using (hasDerivAt_id z0).mul_const a
-  simpa using hderiv.sub hlinear
+  convert! hderiv.sub hlinear using 1 <;> simp
 
 /--
 If the original finite log-MGF has derivative `a` at `-z0`, then the log-MGF
@@ -987,11 +986,11 @@
   have hlinear : HasDerivAt (fun z : ℝ => z * a) a z0 := by
     simpa using (hasDerivAt_id z0).mul_const a
   have hneg : HasDerivAt (fun z : ℝ => -z) (-1) z0 := by
-    simpa using (hasDerivAt_id z0).neg
+    convert! (hasDerivAt_id z0).neg using 1 <;> simp
   have hcomp :
       HasDerivAt (fun z : ℝ => finiteLogMGF μ score (-z)) (-a) z0 := by
-    simpa using hderiv.comp z0 hneg
-  simpa using hlinear.add hcomp
+    convert! hderiv.comp z0 hneg using 1 <;> simp
+  convert! hlinear.add hcomp using 1 <;> simp
 
 /-- Legendre-transform objective at a fixed dual parameter `z`. -/
 def finiteLegendreValue (μ : PMF α) (score : α → ℝ)
@@ -1151,7 +1150,7 @@
       Filter.Tendsto (fun z : ℝ => finiteLogMGF μ score z)
         Filter.atBot
         (nhds (Real.log pZero)) := by
-    simpa [finiteLogMGF] using
+    simpa only [finiteLogMGF, Function.comp_def] using
       (Real.continuousAt_log (ne_of_gt hpZero_pos)).tendsto.comp hmgf
   have hInf :
       sInf (Set.range fun z : ℝ => finiteLogMGF μ score z) =
@@ -1503,7 +1502,7 @@
       Filter.Tendsto (fun z : ℝ => finiteLogMGF μ score z)
         Filter.atBot
         (nhds (Real.log pZero)) := by
-    simpa [finiteLogMGF] using
+    simpa only [finiteLogMGF, Function.comp_def] using
       (Real.continuousAt_log (ne_of_gt hpZero_pos)).tendsto.comp hmgf
   have hneg :
       Filter.Tendsto (fun z : ℝ => -finiteLogMGF μ score z)
```

## AppliedModelingLib/Foundations/Probability/LargeDeviations.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/LargeDeviations.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/LargeDeviations.lean
@@ -2015,7 +2015,7 @@
     (hrate : ∀ i, targetRate < C.rate i) :
     HasExpUpperBoundWithConst
       (C.aggregateError weight) targetRate := by
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
       (ι := ι)
       (p := fun i n => C.errorProb i n)
@@ -2025,6 +2025,7 @@
       hweight
       C.has_rate
       hrate
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 /--
 If every component exact rate is bounded below by a strictly positive floor,
@@ -2062,7 +2063,7 @@
       ∀ i : ι, ∀ᶠ n : ℕ in atTop, 0 ≤ C.errorProb i n := by
     intro i
     exact (C.has_rate i).eventually_pos.mono (fun _ hn => hn.le)
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component
       (ι := ι)
       (p := fun i n => C.errorProb i n)
@@ -2075,6 +2076,7 @@
       hweight_pos
       (C.has_rate i0)
       hrate
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 theorem aggregateError_hasExponentialRate_of_min_component
     [DecidableEq ι]
@@ -2180,7 +2182,7 @@
       exact hcert.hasExpUpperBoundWithConst_of_lt
         (lt_of_lt_of_le hrate hrate_ge)
     · exact HasExpUpperBoundWithConst.of_eventually_zero hzero
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     finite_weighted_sum_hasExpUpperBoundWithConst
       (ι := ι)
       (p := fun i n => C.errorProb i n)
@@ -2190,6 +2192,7 @@
       hweight
       hbound
       (fun _ => le_rfl)
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 /--
 Exact finite aggregate rate from a rate envelope: one positive-weight
@@ -2204,7 +2207,7 @@
     (iMin : ι) (hweight_pos : 0 < weight iMin)
     (hmin : ExponentialRateCertificate (C.errorProb iMin) minRate) :
     HasExponentialRate (C.aggregateError weight) minRate := by
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     finite_weighted_sum_hasExponentialRate_of_min_component_cert_or_eventually_zero
       (ι := ι)
       (p := fun i n => C.errorProb i n)
@@ -2215,6 +2218,7 @@
       hweight_pos
       hmin
       C.component
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 end FiniteErrorRateEnvelopeCertificate
 
@@ -2241,9 +2245,10 @@
         simpa [one_mul] using
           (exponentialRateCertificate_const_mul_exp
             (C := 1) (rate := rate i) zero_lt_one) }
-  simpa [FiniteErrorRateCertificate.aggregateError, C] using
+  have hCompatAggregate :=
     C.aggregateError_hasExponentialRate_of_min_component
       hweight_nonneg iMin hweight_pos hrate_min hrate_ge
+  convert! hCompatAggregate using 1 <;> simp [FiniteErrorRateCertificate.aggregateError, C] <;> rfl
 
 /--
 Certificate form of `finite_exp_sum_hasExponentialRate_of_min_component`.
@@ -2311,7 +2316,7 @@
     (hrate : ∀ hi lo, targetRate ≤ C.rate hi lo) :
     HasExpUpperBoundWithConst
       (C.aggregateError pairWeight) targetRate := by
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     finite_weighted_sum_hasExpUpperBoundWithConst
       (ι := θ × θ)
       (p := fun pair n => C.errorProb pair.1 pair.2 n)
@@ -2321,6 +2326,7 @@
       (fun pair => hweight pair.1 pair.2)
       (fun pair => C.has_bound pair.1 pair.2)
       (fun pair => hrate pair.1 pair.2)
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 end PairwiseErrorUpperBoundCertificate
 
@@ -2366,7 +2372,7 @@
     (hrate : ∀ hi lo, targetRate < C.rate hi lo) :
     HasExpUpperBoundWithConst
       (C.aggregateError pairWeight) targetRate := by
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
       (ι := θ × θ)
       (p := fun pair n => C.errorProb pair.1 pair.2 n)
@@ -2376,6 +2382,7 @@
       (fun pair => hweight pair.1 pair.2)
       (fun pair => C.has_rate pair.1 pair.2)
       (fun pair => hrate pair.1 pair.2)
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 /--
 If all pairwise exact rates are bounded below by a positive floor, the
@@ -2388,13 +2395,14 @@
     (hrateFloor_pos : 0 < rateFloor)
     (hrateFloor : ∀ hi lo, rateFloor ≤ C.rate hi lo) :
     Tendsto (C.aggregateError pairWeight) atTop (nhds 0) := by
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     C.toFiniteErrorRateCertificate.aggregateError_tendsto_zero_of_pos_rate_floor
       (weight := fun pair : θ × θ => pairWeight pair.1 pair.2)
       (rateFloor := rateFloor)
       (fun pair => hweight pair.1 pair.2)
       hrateFloor_pos
       (fun pair => hrateFloor pair.1 pair.2)
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 theorem aggregateError_hasExpLowerBoundWithConst_of_component_gt
     [DecidableEq θ]
@@ -2411,7 +2419,7 @@
     intro pair
     exact (C.has_rate pair.1 pair.2).eventually_pos.mono
       (fun _ hn => hn.le)
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component
       (ι := θ × θ)
       (p := fun pair n => C.errorProb pair.1 pair.2 n)
@@ -2424,6 +2432,7 @@
       hweight_pos
       (C.has_rate hi lo)
       hrate
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 theorem aggregateError_hasExponentialRate_of_min_pair
     [DecidableEq θ]
@@ -2504,12 +2513,13 @@
     (hrate : targetRate < minRate) :
     HasExpUpperBoundWithConst
       (C.aggregateError pairWeight) targetRate := by
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     C.toFiniteErrorRateEnvelopeCertificate
       |>.aggregateError_hasExpUpperBoundWithConst_of_lt
         (weight := fun pair : θ × θ => pairWeight pair.1 pair.2)
         (fun pair => hweight pair.1 pair.2)
         hrate
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 theorem aggregateError_hasExponentialRate_of_min_pair
     [DecidableEq θ]
@@ -2521,7 +2531,7 @@
       ExponentialRateCertificate
         (C.errorProb hiMin loMin) minRate) :
     HasExponentialRate (C.aggregateError pairWeight) minRate := by
-  simpa [aggregateError] using
+  have hCompatAggregate :=
     C.toFiniteErrorRateEnvelopeCertificate
       |>.aggregateError_hasExponentialRate_of_min_component
         (weight := fun pair : θ × θ => pairWeight pair.1 pair.2)
@@ -2529,6 +2539,7 @@
         (hiMin, loMin)
         hweight_pos
         hmin
+  convert! hCompatAggregate using 1 <;> simp [aggregateError] <;> rfl
 
 end PairwiseErrorRateEnvelopeCertificate
```

## PRPKG24AccuracyDiversity/MainTheorems.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/MainTheorems.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/MainTheorems.lean
@@ -4890,25 +4890,25 @@
           boundedTailScale β a) :=
     paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
       (M₀ := M - L) baseMeasure h_base_bounds
-      (by simpa [AppliedModelingLib.Probability.reflectedCDFMass] using tail)
+      (by simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using tail)
       k_pos hwidth_pos
       (by
-        simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+        simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
           AppliedModelingLib.Probability.reflectedCDFMass_measurable baseMeasure M)
       (by
-        simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+        simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
           AppliedModelingLib.Probability.reflectedCDFMass_mono baseMeasure M)
       (by
         intro x
-        simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+        simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
           AppliedModelingLib.Probability.reflectedCDFMass_nonneg baseMeasure M x)
       (by
         intro x
-        simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+        simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
           AppliedModelingLib.Probability.reflectedCDFMass_le_one baseMeasure M x)
       (by
         intro x hx
-        simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+        simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
           AppliedModelingLib.Probability.reflectedCDFMass_eq_one_of_ae_bounds
             baseMeasure h_base_bounds hx)
 
@@ -5089,40 +5089,40 @@
           (AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event
             baseMeasure M x).symm)
       (by
-        simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+        simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
           AppliedModelingLib.Probability.reflectedCDFMass_measurable baseMeasure M)
       (by
         intro x
-        simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+        simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
           AppliedModelingLib.Probability.reflectedCDFMass_nonneg baseMeasure M x)
       (by
         intro x
-        simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+        simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
           AppliedModelingLib.Probability.reflectedCDFMass_le_one baseMeasure M x)
       (by
         intro x hx
-        simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+        simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
           AppliedModelingLib.Probability.reflectedCDFMass_eq_one_of_ae_bounds
             baseMeasure h_base_bounds hx))
     tail
     (by
-      simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+      simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
         AppliedModelingLib.Probability.reflectedCDFMass_measurable baseMeasure M)
     k_pos hwidth_pos
     (by
-      simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+      simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
         AppliedModelingLib.Probability.reflectedCDFMass_mono baseMeasure M)
     (by
       intro x
-      simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+      simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
         AppliedModelingLib.Probability.reflectedCDFMass_nonneg baseMeasure M x)
     (by
       intro x
-      simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+      simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
         AppliedModelingLib.Probability.reflectedCDFMass_le_one baseMeasure M x)
     (by
       intro x hx
-      simpa [AppliedModelingLib.Probability.reflectedCDFMass] using
+      simpa only [show AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M = (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) from funext (fun x => AppliedModelingLib.Probability.reflectedCDFMass_eq_sub_event baseMeasure M x)] using
         AppliedModelingLib.Probability.reflectedCDFMass_eq_one_of_ae_bounds
           baseMeasure h_base_bounds hx)
 
@@ -7783,9 +7783,9 @@
     paper_example1_top_one_exponential_harmonic_calibrated
       hp1 hp2 hlambda seq
   constructor
-  · simpa [paper_example1_gamma_one_targetShare_romance hp_sum] using
+  · simpa [paper_example1_gamma_one_targetShare_romance hp_sum, OptimalAllocationSequence.toAllocationSequence, AllocationSequence.representation] using
       hconv (0 : ItemType 2)
-  · simpa [paper_example1_gamma_one_targetShare_action hp_sum] using
+  · simpa [paper_example1_gamma_one_targetShare_action hp_sum, OptimalAllocationSequence.toAllocationSequence, AllocationSequence.representation] using
       hconv (1 : ItemType 2)
 
 /--
@@ -9822,7 +9822,7 @@
     Proposition4AveragingCertificate.ofFiniteUniformAverage
       gamma rho uniformProfile uniformValue uniform_gamma_eq
       average_rho_eq_uniformValue rho_le_gamma
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, finite-user averaging endpoint with `Gamma` instantiated
@@ -9846,7 +9846,7 @@
     Proposition4AveragingCertificate.ofFiniteUniformAverageOfSupremum
       gamma rho uniformProfile uniformValue uniform_gamma_eq
       average_rho_eq_uniformValue rho_bddAbove gamma_eq_sSup_range
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4 Laplace bridge: exact-rate uniqueness turns a source
@@ -10077,7 +10077,7 @@
     Proposition4AveragingCertificate.ofProbabilityIntegralAverage
       userMeasure gamma rho uniformProfile uniformValue rho_integrable
       uniform_gamma_eq integral_rho_eq_uniformValue rho_le_gamma
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, probability-user averaging endpoint with `Gamma`
@@ -10104,7 +10104,7 @@
       userMeasure gamma rho uniformProfile uniformValue rho_integrable
       uniform_gamma_eq integral_rho_eq_uniformValue rho_bddAbove
       gamma_eq_sSup_range
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, probability-user averaging endpoint with `Gamma`
@@ -10161,7 +10161,7 @@
       hsource hopen hF_int hw_int hWpos hcpos hw_lower hw_bound
       rho_integrable uniform_gamma_eq integral_rho_eq_uniformValue
       x0 hmax hx0 hcont
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, probability-user averaging endpoint with `Gamma`
@@ -10299,7 +10299,7 @@
       userMeasure profileMeasure profile_probability gamma kernel
       uniformProfile uniformValue rho_integrable uniform_gamma_eq
       integral_kernel_swap kernel_user_integral_eq rho_le_gamma
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, probability-kernel averaging endpoint with `Gamma`
@@ -10344,7 +10344,7 @@
       uniformProfile uniformValue rho_integrable uniform_gamma_eq
       integral_kernel_swap kernel_user_integral_eq rho_bddAbove
       gamma_eq_sSup_range
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, product-integrable probability-kernel averaging endpoint.
@@ -10380,7 +10380,7 @@
       userMeasure profileMeasure profile_probability gamma kernel
       uniformProfile uniformValue kernel_integrable uniform_gamma_eq
       kernel_user_integral_eq rho_le_gamma
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, product-integrable probability-kernel averaging endpoint
@@ -10422,7 +10422,7 @@
       userMeasure profileMeasure profile_probability gamma kernel
       uniformProfile uniformValue kernel_integrable uniform_gamma_eq
       kernel_user_integral_eq rho_bddAbove gamma_eq_sSup_range
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, product-integrable probability-kernel averaging endpoint
@@ -10500,7 +10500,7 @@
       W c uniformProfile uniformValue hsource hopen hF_int hw_int hWpos
       hcpos hw_lower hw_bound kernel_integrable uniform_gamma_eq
       kernel_user_integral_eq x0 hmax hx0 hcont
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, product-integrable probability-kernel averaging endpoint
@@ -10814,7 +10814,7 @@
       userAction itemAction anchor userAction_measurePreserving
       userAction_measurableEmbedding kernel_diagonal_invariant
       itemAction_transitive anchor_integral_eq_uniformValue rho_le_gamma
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, symmetry-driven product-integrable probability-kernel
@@ -10874,7 +10874,7 @@
       userAction_measurableEmbedding kernel_diagonal_invariant
       itemAction_transitive anchor_integral_eq_uniformValue rho_bddAbove
       gamma_eq_sSup_range
-  simpa [C] using C.uniform_minimizes
+  exact C.uniform_minimizes
 
 /--
 Source Proposition 4, two-measure probability-kernel endpoint.
@@ -11105,7 +11105,7 @@
       userMeasure profileMeasure profile_probability gamma kernel
       uniformProfile uniformValue C kernel_aestronglyMeasurable
       kernel_norm_le uniform_gamma_eq kernel_user_integral_eq rho_le_gamma
-  simpa [Ccert] using Ccert.uniform_minimizes
+  exact Ccert.uniform_minimizes
 
 /--
 Source Proposition 4, bounded probability-kernel averaging endpoint with
@@ -11151,7 +11151,7 @@
       uniformProfile uniformValue C kernel_aestronglyMeasurable
       kernel_norm_le uniform_gamma_eq kernel_user_integral_eq
       rho_bddAbove gamma_eq_sSup_range
-  simpa [Ccert] using Ccert.uniform_minimizes
+  exact Ccert.uniform_minimizes
 
 /--
 Source Theorem 2(i), decaying Bernoulli success probabilities with `α < 1`,
@@ -12811,7 +12811,7 @@
     paper_theorem3_varying_success_probability_log_share_sequence
       B hprob_pos hprob_lt_one hlike_pos seq
   intro t
-  simpa [OptimalAllocationSequence.toAllocationSequence,
+  simpa [OptimalAllocationSequence.toAllocationSequence, AllocationSequence.representation,
     theorem3LogShareProfile_targetShare_eq B hprob_pos hprob_lt_one t] using
     hconv t
```

## PRPKG24AccuracyDiversity/AppendixD2DensitySource.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/AppendixD2DensitySource.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/AppendixD2DensitySource.lean
@@ -104,7 +104,8 @@
       filter_upwards [h_base_bounds] with y hy
       exact not_lt_of_ge hy.2
     have hzero := MeasureTheory.ae_iff.mp hnot
-    simpa only [Set.mem_Ioi, not_not] using hzero
+    simp only [not_not] at hzero
+    exact hzero
   have hdensity_zero :
       MeasureTheory.volume
           ({y | ENNReal.ofReal (f y) ≠ 0} ∩ Set.Ioi M) = 0 := by
```

## PRPKG24AccuracyDiversity/Theorem1PmfSource.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/Theorem1PmfSource.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/Theorem1PmfSource.lean
@@ -36,8 +36,7 @@
         (boundedIidOrderStatisticMeanSeq baseMeasure) k q =
       AppliedModelingLib.Probability.expectedSampleTopKSum
         (definition3IidSampleMeasure baseMeasure q) k
-  simpa [boundedIidOrderStatisticMeanSeq, definition3IidOrderStatisticMean,
-    definition3IidSampleMeasure] using
+  exact
     definition3_iid_orderStatisticTopKSum_eq_expectedSampleTopKSum
       baseMeasure h_finite_mean k q
 
@@ -72,7 +71,7 @@
         AppliedModelingLib.Probability.expectedSampleTopKSum (M.iidProductMeasure (q + 1)) k =
             ∫ sample, exponentialFiniteSampleTopKSum k sample
               ∂M.iidProductMeasure (q + 1) := by
-            simpa [M, exponentialFiniteSampleTopKSum] using
+            exact
               AppliedModelingLib.Probability.expectedSampleTopKSum_eq_integral_topKSumOn_of_ae_nonneg
                 (M.iidProductMeasure (q + 1)) k
                 (M.iidProductMeasure_all_nonnegative_ae (q + 1))
```

## AppliedModelingLib/Foundations/Probability/IIDLargeDeviations.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/IIDLargeDeviations.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/IIDLargeDeviations.lean
@@ -1554,7 +1554,7 @@
     μ score hupper
     (finiteIidScoreTailLowerCertificate_of_tilted_window
       (μ := μ) (score := score) hz hlowerConst_pos hwindow)
-    (by simpa using hrate)
+    (by simpa [finiteIidScoreTailLowerCertificate_of_tilted_window] using hrate)
 
 /--
 Tilted-window finite iid Cramer certificate with the Chernoff upper side
@@ -1984,9 +1984,7 @@
   rate := finiteIidPairwiseScoreGapChernoffRate μ score
   has_rate := by
     intro hi lo
-    simpa [finiteIidPairwiseScoreGapLeftTailProb,
-      finiteIidPairwiseScoreGapChernoffRate,
-      FiniteIidScoreGapCramerCertificate] using
+    exact
       (cramer hi lo).exponentialRateCertificate
 
 /--
@@ -2210,7 +2208,7 @@
     HasExpUpperBoundWithConst
       (finiteIidScoreGapLeftTailProb μ hiScore loScore)
       (-(finiteLogMGF μ (fun a => hiScore a - loScore a) z)) := by
-  simpa [finiteIidScoreGapLeftTailProb] using
+  exact
     finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_mgf_le_exp_neg
       (μ := μ) (score := fun a => hiScore a - loScore a)
       (z := z)
@@ -2232,7 +2230,7 @@
       rate ≤ -finiteLogMGF μ (fun a => hiScore a - loScore a) z) :
     HasExpUpperBoundWithConst
       (finiteIidScoreGapLeftTailProb μ hiScore loScore) rate := by
-  simpa [finiteIidScoreGapLeftTailProb] using
+  exact
     finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
       (μ := μ) (score := fun a => hiScore a - loScore a)
       (z := z) (rate := rate) hz hrate
@@ -2251,7 +2249,7 @@
         HasExpUpperBoundWithConst
           (finiteIidScoreGapLeftTailProb μ hiScore loScore) targetRate := by
   intro targetRate htarget
-  simpa [finiteIidScoreGapLeftTailProb] using
+  exact
     finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate
       (μ := μ) (score := fun a => hiScore a - loScore a)
       hmean hbdd targetRate htarget
@@ -2273,7 +2271,7 @@
         HasExpUpperBoundWithConst
           (finiteIidScoreGapLeftTailProb μ hiScore loScore) targetRate := by
   intro targetRate htarget
-  simpa [finiteIidScoreGapLeftTailProb] using
+  exact
     finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
       (μ := μ) (score := fun a => hiScore a - loScore a)
       hmean hmassPos hgapPos hmassNeg hgapNeg targetRate htarget
@@ -2289,7 +2287,7 @@
       0 < rate ∧
         HasExpUpperBoundWithConst
           (finiteIidScoreGapLeftTailProb μ hiScore loScore) rate := by
-  simpa [finiteIidScoreGapLeftTailProb] using
+  exact
     finiteIidScoreLeftTail_exists_pos_expUpperBoundWithConst_of_pmfExp_pos
       (μ := μ) (score := fun a => hiScore a - loScore a) hmean
 
@@ -2303,8 +2301,7 @@
     ExponentialRateCertificate
       (finiteIidScoreGapLeftTailProb μ hiScore loScore)
       (finiteScoreGapChernoffRate μ hiScore loScore) := by
-  simpa [finiteIidScoreGapLeftTailProb, finiteScoreGapChernoffRate,
-    FiniteIidScoreGapCramerCertificate] using
+  exact
     C.exponentialRateCertificate
 
 /--
@@ -2331,7 +2328,7 @@
     finiteIidScoreGapCramerCertificate_of_pathLower
       μ hiScore loScore
       (fun targetRate htarget => by
-        simpa [finiteIidScoreGapLeftTailProb] using
+        exact
           hupper targetRate
             (by simpa [finiteScoreGapChernoffRate] using htarget))
       C
@@ -2361,7 +2358,7 @@
     finiteIidScoreGapCramerCertificate_of_tailLower
       μ hiScore loScore
       (fun targetRate htarget => by
-        simpa [finiteIidScoreGapLeftTailProb] using
+        exact
           hupper targetRate
             (by simpa [finiteScoreGapChernoffRate] using htarget))
       C
@@ -2405,7 +2402,7 @@
     finiteIidScoreGapCramerCertificate_of_tilted_window
       μ hiScore loScore
       (fun targetRate htarget => by
-        simpa [finiteIidScoreGapLeftTailProb] using
+        exact
           hupper targetRate
             (by simpa [finiteScoreGapChernoffRate] using htarget))
       hz hlowerConst_pos hwindow
@@ -2527,7 +2524,7 @@
     HasExpUpperBoundWithConst
       (finiteIidScoreGapLeftTailProb μ hiScore loScore)
       (ternaryGapClosedChernoffRate pUp pDown) := by
-  simpa [finiteIidScoreGapLeftTailProb] using
+  exact
     finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_ternaryGapMGF
       (μ := μ) (score := fun a => hiScore a - loScore a)
       hUp hDown hle hsum hmgf
@@ -2662,7 +2659,7 @@
     ExponentialRateCertificate
       (finiteIidScoreGapLeftTailProb μ hiScore loScore)
       (ternaryGapClosedChernoffRate pUp pDown) := by
-  simpa [finiteIidScoreGapLeftTailProb] using
+  exact
     finiteIidScoreLeftTail_exponentialRateCertificate_of_ternary_scores
       (μ := μ) (score := fun a => hiScore a - loScore a)
       hUp hDown hle hscore hUpProb hDownProb
```

## AppliedModelingLib/Foundations/Probability/FiniteProductMultinomialCounts.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/FiniteProductMultinomialCounts.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/FiniteProductMultinomialCounts.lean
@@ -1,3 +1,4 @@
+import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
 import AppliedModelingLib.Foundations.Probability.IIDLargeDeviations
 import Mathlib.Data.Finset.Preimage
 import Mathlib.Data.Fintype.EquivFin
@@ -946,7 +947,7 @@
         (fun a _ha => pow_nonneg ENNReal.toReal_nonneg _)
     have htype_le_one : typeMass ≤ 1 := by
       dsimp [typeMass]
-      exact Finset.prod_le_one
+      exact Finset.prod_le_one₀
         (fun a _ha => pow_nonneg ENNReal.toReal_nonneg _)
         (fun a _ha =>
           pow_le_one₀ ENNReal.toReal_nonneg (pmf_apply_toReal_le_one μ a))
@@ -1360,7 +1361,7 @@
       μ score hmean hmassPos hscorePos hmassNeg hscoreNeg)
     (fun targetRate htarget => by
       rcases hlower targetRate htarget with ⟨C, hC⟩
-      exact ⟨C.toPathLowerCertificate, by simpa using hC⟩)
+      exact ⟨C.toPathLowerCertificate, by simpa [FiniteIidScoreCountVectorLowerCertificate.toPathLowerCertificate, FiniteIidScoreCountVectorLowerCertificate.toBucketLowerCertificate, FiniteIidScoreBucketLowerCertificate.toPathLowerCertificate] using hC⟩)
 
 /--
 Score-gap form of
```

## AppliedModelingLib/Foundations/Probability/FiniteEmpiricalMultinomialCounts.lean

```diff
--- upstream/AppliedModelingLib/Foundations/Probability/FiniteEmpiricalMultinomialCounts.lean
+++ lean-4.34.1/AppliedModelingLib/Foundations/Probability/FiniteEmpiricalMultinomialCounts.lean
@@ -1,3 +1,4 @@
+import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
 import AppliedModelingLib.Foundations.Math.SimplexRounding
 import AppliedModelingLib.Foundations.Probability.FiniteProductMultinomialCounts
 
@@ -749,7 +750,7 @@
           = ∏ a : α, q a ^ k a * Nat.factorial (q a) := by
             rw [Finset.prod_mul_distrib]
       _ ≤ ∏ a : α, q a ^ q a * Nat.factorial (k a) := by
-            exact Finset.prod_le_prod
+            exact Finset.prod_le_prod₀
               (fun _a _ha => Nat.zero_le _)
               (fun a _ha => hcoord a)
       _ = (∏ a : α, q a ^ q a) *
@@ -2325,7 +2326,7 @@
       μ score hmean hmassPos hscorePos hmassNeg hscoreNeg)
     (fun targetRate htarget => by
       rcases hlower targetRate htarget with ⟨C, hC⟩
-      exact ⟨C.toTailLowerCertificate, by simpa using hC⟩)
+      exact ⟨C.toTailLowerCertificate, by simpa [FiniteIidScoreEmpiricalTypeLowerCertificate.toTailLowerCertificate] using hC⟩)
 
 /--
 Score-gap form of
```

## AppliedModelingLib/Applications/RatingSystems/FiniteComparison.lean

```diff
--- upstream/AppliedModelingLib/Applications/RatingSystems/FiniteComparison.lean
+++ lean-4.34.1/AppliedModelingLib/Applications/RatingSystems/FiniteComparison.lean
@@ -91,7 +91,7 @@
   have hderiv_finite :
       HasDerivAt
         (fun z : ℝ => finiteLogMGF (M.typeLaw θ) M.score z) a z0 := by
-    simpa [FiniteRatingLDPModel.logMGF] using hderiv
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv
   have hderiv_formula := finiteLogMGF_hasDerivAt (M.typeLaw θ) M.score z0
   have ha_formula :
       ((∑ r : Rating,
@@ -158,7 +158,7 @@
   have hderiv_finite :
       HasDerivAt
         (fun z : ℝ => finiteLogMGF (M.typeLaw θ) M.score z) a z0 := by
-    simpa [FiniteRatingLDPModel.logMGF] using hderiv
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv
   have hderiv_formula := finiteLogMGF_hasDerivAt (M.typeLaw θ) M.score z0
   have ha_formula :
       ((∑ r : Rating,
@@ -836,12 +836,12 @@
   have hderiv_hi :
       HasDerivAt (fun t : ℝ => M.logMGF hi t)
         (AppliedModelingLib.pmfExp (M.typeLaw hi) M.score) 0 := by
-    simpa [FiniteRatingLDPModel.logMGF] using
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using
       finiteLogMGF_hasDerivAt_zero (M.typeLaw hi) M.score
   have hderiv_lo :
       HasDerivAt (fun t : ℝ => M.logMGF lo t)
         (AppliedModelingLib.pmfExp (M.typeLaw lo) M.score) 0 := by
-    simpa [FiniteRatingLDPModel.logMGF] using
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using
       finiteLogMGF_hasDerivAt_zero (M.typeLaw lo) M.score
   have hhi_inner :
       HasDerivAt (fun t : ℝ => t * (sampleRate hi)⁻¹)
@@ -850,8 +850,7 @@
   have hlo_inner :
       HasDerivAt (fun t : ℝ => -(t * (sampleRate lo)⁻¹))
         (-(sampleRate lo)⁻¹) 0 := by
-    simpa using
-      ((hasDerivAt_id (0 : ℝ)).mul_const ((sampleRate lo)⁻¹)).neg
+    convert! ((hasDerivAt_id (0 : ℝ)).mul_const ((sampleRate lo)⁻¹)).neg using 1 <;> simp <;> rfl
   have hderiv_hi_scaled :
       HasDerivAt (fun t : ℝ => M.logMGF hi t)
         (AppliedModelingLib.pmfExp (M.typeLaw hi) M.score)
@@ -1045,7 +1044,7 @@
         zHi := by
     have hformula := finiteLogMGF_hasDerivAt (M.typeLaw hi) M.score zHi
     rw [pmfExp_finiteExponentialTilt_eq]
-    simpa [FiniteRatingLDPModel.logMGF] using hformula
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hformula
   have hderiv_lo :
       HasDerivAt (fun t : ℝ => M.logMGF lo t)
         (AppliedModelingLib.pmfExp
@@ -1053,7 +1052,7 @@
         zLo := by
     have hformula := finiteLogMGF_hasDerivAt (M.typeLaw lo) M.score zLo
     rw [pmfExp_finiteExponentialTilt_eq]
-    simpa [FiniteRatingLDPModel.logMGF] using hformula
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hformula
   have hhi_inner :
       HasDerivAt (fun t : ℝ => t * (sampleRate hi)⁻¹)
         ((sampleRate hi)⁻¹) z := by
@@ -1061,7 +1060,7 @@
   have hlo_inner :
       HasDerivAt (fun t : ℝ => -(t * (sampleRate lo)⁻¹))
         (-(sampleRate lo)⁻¹) z := by
-    simpa using ((hasDerivAt_id z).mul_const ((sampleRate lo)⁻¹)).neg
+    convert! ((hasDerivAt_id z).mul_const ((sampleRate lo)⁻¹)).neg using 1 <;> simp <;> rfl
   have hhi_comp :
       HasDerivAt
         (fun t : ℝ => M.logMGF hi (t * (sampleRate hi)⁻¹))
@@ -1624,7 +1623,8 @@
         withTopRealScale (sampleRate lo)
           (finiteLegendreValue (M.typeLaw lo) M.score b zLo : WithTop ℝ) ≤
       pairwiseRateObjectiveTop M sampleRate hi lo b := by
-    simpa [pairwiseRateObjectiveTop] using add_le_add hhi_ge_b hlo_ge_b
+    unfold pairwiseRateObjectiveTop
+    exact add_le_add hhi_ge_b hlo_ge_b
   have hcancel_real :
       sampleRate hi * finiteLegendreValue (M.typeLaw hi) M.score a zHi +
           sampleRate lo * finiteLegendreValue (M.typeLaw lo) M.score a zLo =
@@ -1777,7 +1777,7 @@
       FiniteRatingLDPModel.logMGF] using
       finiteRateFunction_eq_eval_of_logMGF_hasDerivAt_no_bdd
         (M.typeLaw hi) M.score a (z * (sampleRate hi)⁻¹)
-        (by simpa [FiniteRatingLDPModel.logMGF] using hderiv_hi)
+        (by simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv_hi)
   have hlo_real :
       M.rateFunction lo a =
         finiteLegendreValue (M.typeLaw lo) M.score a zLo := by
@@ -1786,7 +1786,7 @@
       FiniteRatingLDPModel.logMGF] using
       finiteRateFunction_eq_eval_of_logMGF_hasDerivAt_no_bdd
         (M.typeLaw lo) M.score a (-(z * (sampleRate lo)⁻¹))
-        (by simpa [FiniteRatingLDPModel.logMGF] using hderiv_lo)
+        (by simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv_lo)
   simp [pairwiseRateObjectiveTop,
     FiniteRatingLDPModel.pairwiseRateObjectiveTop,
     FiniteRatingLDPModel.pairwiseRateObjective,
@@ -1869,7 +1869,7 @@
   have hlo_inner :
       HasDerivAt (fun t : ℝ => -(t * (sampleRate lo)⁻¹))
         (-(sampleRate lo)⁻¹) z := by
-    simpa using ((hasDerivAt_id z).mul_const ((sampleRate lo)⁻¹)).neg
+    convert! ((hasDerivAt_id z).mul_const ((sampleRate lo)⁻¹)).neg using 1 <;> simp <;> rfl
   have hhi_comp :
       HasDerivAt (fun t : ℝ => M.logMGF hi (t * (sampleRate hi)⁻¹))
         (aHi * (sampleRate hi)⁻¹) z :=
@@ -4491,7 +4491,7 @@
         Filter.Tendsto (fun k : ℕ => z * coeffHi k)
           Filter.atTop (nhds (z * (sampleRate hi)⁻¹)) :=
       hcoeffHi.const_mul z
-    simpa [FiniteRatingLDPModel.logMGF] using
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using
       (finiteLogMGF_continuous (M.typeLaw hi) M.score).continuousAt.tendsto.comp
         harg
   have hlogLo :
@@ -4503,7 +4503,7 @@
         Filter.Tendsto (fun k : ℕ => -(z * coeffLo k))
           Filter.atTop (nhds (-(z * (sampleRate lo)⁻¹))) :=
       (hcoeffLo.const_mul z).neg
-    simpa [FiniteRatingLDPModel.logMGF] using
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using
       (finiteLogMGF_continuous (M.typeLaw lo) M.score).continuousAt.tendsto.comp
         harg
   have hfloorLog :
@@ -4989,11 +4989,11 @@
   have hderiv_hi_finite :
       HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw hi) M.score t) a
         (z * (sampleRate hi)⁻¹) := by
-    simpa [FiniteRatingLDPModel.logMGF] using hderiv_hi
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv_hi
   have hderiv_lo_finite :
       HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw lo) M.score t) a
         (-(z * (sampleRate lo)⁻¹)) := by
-    simpa [FiniteRatingLDPModel.logMGF] using hderiv_lo
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv_lo
   have hdual_hi_nonpos : z * (sampleRate hi)⁻¹ ≤ 0 :=
     mul_nonpos_of_nonpos_of_nonneg hz (inv_nonneg.mpr hgHi.le)
   have hdual_lo_nonneg : 0 ≤ -(z * (sampleRate lo)⁻¹) := by
@@ -5627,11 +5627,11 @@
   have hderiv_hi_finite :
       HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw hi) M.score t) a
         (z * (sampleRate hi)⁻¹) := by
-    simpa [FiniteRatingLDPModel.logMGF] using hderiv_hi
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv_hi
   have hderiv_lo_finite :
       HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw lo) M.score t) a
         (-(z * (sampleRate lo)⁻¹)) := by
-    simpa [FiniteRatingLDPModel.logMGF] using hderiv_lo
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv_lo
   have C_hi :
       FiniteIidScoreCramerCertificate (M.typeLaw hi)
         (fun r : Rating => M.score r - a) :=
@@ -5752,11 +5752,11 @@
   have hderiv_hi_finite :
       HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw hi) M.score t) a
         (z * (sampleRate hi)⁻¹) := by
-    simpa [FiniteRatingLDPModel.logMGF] using hderiv_hi
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv_hi
   have hderiv_lo_finite :
       HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw lo) M.score t) a
         (-(z * (sampleRate lo)⁻¹)) := by
-    simpa [FiniteRatingLDPModel.logMGF] using hderiv_lo
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hderiv_lo
   have hdual_hi_nonpos : z * (sampleRate hi)⁻¹ ≤ 0 :=
     mul_nonpos_of_nonpos_of_nonneg hz (inv_nonneg.mpr hgHi.le)
   have hdual_lo_nonneg : 0 ≤ -(z * (sampleRate lo)⁻¹) := by
@@ -6360,7 +6360,7 @@
   have hlo_inner :
       HasDerivAt (fun t : ℝ => -(t * (gLo : ℝ)⁻¹))
         (-(gLo : ℝ)⁻¹) z := by
-    simpa using ((hasDerivAt_id z).mul_const ((gLo : ℝ)⁻¹)).neg
+    convert! ((hasDerivAt_id z).mul_const ((gLo : ℝ)⁻¹)).neg using 1 <;> simp <;> rfl
   have hhi_comp :
       HasDerivAt (fun t : ℝ => M.logMGF hi (t * (gHi : ℝ)⁻¹))
         (a * (gHi : ℝ)⁻¹) z :=
@@ -6440,7 +6440,7 @@
   have hlo_inner :
       HasDerivAt (fun t : ℝ => -(t * (gLo : ℝ)⁻¹))
         (-(gLo : ℝ)⁻¹) z := by
-    simpa using ((hasDerivAt_id z).mul_const ((gLo : ℝ)⁻¹)).neg
+    convert! ((hasDerivAt_id z).mul_const ((gLo : ℝ)⁻¹)).neg using 1 <;> simp <;> rfl
   have hhi_comp :
       HasDerivAt (fun t : ℝ => M.logMGF hi (t * (gHi : ℝ)⁻¹))
         (aHi * (gHi : ℝ)⁻¹) z :=
@@ -6522,7 +6522,7 @@
     ExponentialRateCertificate
       (twoSampleRateBlockErrorProb M hi lo gHi gLo)
       (twoSampleRateBlockChernoffRate M hi lo gHi gLo) := by
-  simpa [twoSampleRateBlockErrorProb, twoSampleRateBlockChernoffRate] using
+  exact
     C.exponentialRateCertificate
 
 /--
@@ -7381,9 +7381,7 @@
       targetRate := by
   let E :=
     C.toFloorPkComplementErrorRateCertificate M sampleRate pairHi pairLo
-  simpa [FiniteErrorRateCertificate.aggregateError, E,
-    PairwiseThresholdRateTopLdpCertificate.toFloorPkComplementErrorRateCertificate,
-    finiteFloorPkComplementError] using
+  exact
     E.aggregateError_hasExpUpperBoundWithConst_of_lt hweight hrate
 
 /--
@@ -7405,9 +7403,7 @@
       (C.rate pMin) := by
   let E :=
     C.toFloorPkComplementErrorRateCertificate M sampleRate pairHi pairLo
-  simpa [FiniteErrorRateCertificate.aggregateError, E,
-    PairwiseThresholdRateTopLdpCertificate.toFloorPkComplementErrorRateCertificate,
-    finiteFloorPkComplementError] using
+  exact
     E.aggregateError_hasExponentialRate_of_min_component
       hweight_nonneg pMin hweight_pos rfl hrate_ge
 
@@ -7823,7 +7819,7 @@
     ExponentialRateCertificate
       (equalSamplePairwiseErrorProb M hi lo)
       (equalSamplePairwiseChernoffRate M hi lo) := by
-  simpa [equalSamplePairwiseErrorProb, equalSamplePairwiseChernoffRate] using
+  exact
     C.exponentialRateCertificate
 
 theorem ratingLogMGF_eq_finite_formula
```

## AppliedModelingLib/Applications/RatingSystems/BinaryLargeDeviations.lean

```diff
--- upstream/AppliedModelingLib/Applications/RatingSystems/BinaryLargeDeviations.lean
+++ lean-4.34.1/AppliedModelingLib/Applications/RatingSystems/BinaryLargeDeviations.lean
@@ -704,7 +704,7 @@
     have h :=
       bernoulliHellingerBase_left_interiorEqualSplit_eq_common_div
         hpLo0 hpHi1 hlt
-    simpa [N, D, a, b, c, d] using h
+    simpa [N, D, a, b, c, d, bernoulliInteriorSplitDenominator, bernoulliInteriorFailureSplitNumerator, bernoulliInteriorSuccessSplitNumerator] using h
   have hD : D = 2 * (1 - H) := by
     dsimp [D, H]
     nlinarith [hac, hbd]
@@ -1261,8 +1261,7 @@
       HasDerivAt (fun x : ℝ => (1 - x) ^ aLo)
         ((-1) * aLo * (1 - pLo) ^ (aLo - 1)) pLo := by
     have hbase : HasDerivAt (fun x : ℝ => 1 - x) (-1) pLo := by
-      simpa using (hasDerivAt_const (c := (1 : ℝ)) pLo).sub
-        (hasDerivAt_id pLo)
+      convert! (hasDerivAt_const (c := (1 : ℝ)) pLo).sub (hasDerivAt_id pLo) using 1 <;> simp <;> rfl
     simpa using
       hbase.rpow_const (p := aLo)
         (Or.inl (ne_of_gt (sub_pos.mpr hpLo1)))
@@ -1286,9 +1285,8 @@
           pLo ^ (gLo / (gHi + gLo) - 1)) *
           pHi ^ aHi) pLo :=
     hsucc_var.mul_const (pHi ^ aHi)
-  simpa [weightedBernoulliClosedRateBase, weightedBernoulliFailureBase,
-    weightedBernoulliSuccessBase, aLo, aHi, add_comm, add_left_comm, add_assoc]
-    using hfail.add hsucc
+  unfold weightedBernoulliClosedRateBase weightedBernoulliFailureBase weightedBernoulliSuccessBase
+  convert! hfail.add hsucc using 1 <;> simp [aLo, aHi, add_comm, add_left_comm, add_assoc] <;> rfl
 
 /-- Derivative of the closed-rate base with respect to the higher endpoint. -/
 theorem weightedBernoulliClosedRateBase_hasDerivAt_hi
@@ -1307,8 +1305,7 @@
       HasDerivAt (fun x : ℝ => (1 - x) ^ aHi)
         ((-1) * aHi * (1 - pHi) ^ (aHi - 1)) pHi := by
     have hbase : HasDerivAt (fun x : ℝ => 1 - x) (-1) pHi := by
-      simpa using (hasDerivAt_const (c := (1 : ℝ)) pHi).sub
-        (hasDerivAt_id pHi)
+      convert! (hasDerivAt_const (c := (1 : ℝ)) pHi).sub (hasDerivAt_id pHi) using 1 <;> simp <;> rfl
     simpa using
       hbase.rpow_const (p := aHi)
         (Or.inl (ne_of_gt (sub_pos.mpr hpHi1)))
@@ -1332,9 +1329,8 @@
           ((gHi / (gHi + gLo)) *
             pHi ^ (gHi / (gHi + gLo) - 1))) pHi :=
     hsucc_var.const_mul (pLo ^ aLo)
-  simpa [weightedBernoulliClosedRateBase, weightedBernoulliFailureBase,
-    weightedBernoulliSuccessBase, aLo, aHi, add_comm, add_left_comm, add_assoc,
-    mul_comm, mul_left_comm, mul_assoc] using hfail.add hsucc
+  unfold weightedBernoulliClosedRateBase weightedBernoulliFailureBase weightedBernoulliSuccessBase
+  convert! hfail.add hsucc using 1 <;> simp [aLo, aHi, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] <;> rfl
 
 /--
 Interior inverse for the Bernoulli binary log-MGF derivative.
@@ -4048,10 +4044,8 @@
     have hsuccHi_pow :
         ContinuousAt (fun q : ℝ × ℝ => q.1 ^ aHi) (pHi, pLo) :=
       hsuccHi.rpow_const (Or.inl (ne_of_gt hpHi0))
-    simpa [weightedBernoulliClosedRateBase,
-      weightedBernoulliFailureBase, weightedBernoulliSuccessBase, aLo, aHi]
-      using (hfailLo_pow.mul hfailHi_pow).add
-        (hsuccLo_pow.mul hsuccHi_pow)
+    unfold weightedBernoulliClosedRateBase weightedBernoulliFailureBase weightedBernoulliSuccessBase
+    convert! (hfailLo_pow.mul hfailHi_pow).add (hsuccLo_pow.mul hsuccHi_pow) using 1 <;> simp [aLo, aHi] <;> rfl
   have hbase_pos :
       0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo :=
     weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
@@ -4098,9 +4092,11 @@
   let aHi : ι → ℝ := fun x => gHi x / denom x
   let AHi : ℝ := GHi / Denom
   have haLo : Filter.Tendsto aLo l (nhds ALo) := by
-    simpa [aLo, ALo, denom, Denom] using hgLo.div hdenom hDenom_ne
+    unfold aLo ALo
+    convert! hgLo.div hdenom hDenom_ne using 1 <;> simp [denom, Denom] <;> rfl
   have haHi : Filter.Tendsto aHi l (nhds AHi) := by
-    simpa [aHi, AHi, denom, Denom] using hgHi.div hdenom hDenom_ne
+    unfold aHi AHi
+    convert! hgHi.div hdenom hDenom_ne using 1 <;> simp [denom, Denom] <;> rfl
   have hfailLo :
       Filter.Tendsto (fun x : ι => 1 - pLo x) l (nhds (1 - PLo)) := by
     simpa using tendsto_const_nhds.sub hpLo
@@ -4215,7 +4211,7 @@
   have hself :
       weightedBernoulliClosedThresholdRate gHi gLo p p = 0 :=
     weightedBernoulliClosedThresholdRate_self hgHi hgLo hp0 hp1
-  simpa [hself] using hcont.tendsto.comp hpair
+  simpa only [hself, Function.comp_def] using hcont.tendsto.comp hpair
 
 /--
 Moving-parameter continuity of the clipped high-endpoint selector on the
@@ -5612,7 +5608,8 @@
       ((realBernoulliPMF (successProb x) (hprob0 x) (hprob1 x) b).toReal :
         ℝ) := by
   cases b
-  · simpa using (measurable_const.sub hprob_meas)
+  · have h : Measurable (fun x => (1 : ℝ) - successProb x) := measurable_const.sub hprob_meas
+    simpa only [realBernoulliPMF_apply_false_toReal] using h
   · simpa using hprob_meas
 
 /--
```

## PRPKG24AccuracyDiversity/Theorem2RankBernoulliSource.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/Theorem2RankBernoulliSource.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/Theorem2RankBernoulliSource.lean
@@ -122,7 +122,7 @@
         (μ j b).toReal *
           (if j = i then binaryRatingScore b else 1) := by
           symm
-          simpa using
+          simpa only [Fintype.piFinset_univ] using
             (Finset.prod_univ_sum
               (t := fun _j : Fin q => (Finset.univ : Finset Bool))
               (f := fun j b =>
```

## PRPKG24AccuracyDiversity/AppendixD1GenericII.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/AppendixD1GenericII.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/AppendixD1GenericII.lean
@@ -123,7 +123,7 @@
     have hbase :=
       (tendsto_rpow_neg_atTop (neg_pos.mpr hsigma_neg)).comp
         tendsto_natCast_atTop_atTop
-    simpa only [neg_neg, Function.comp_apply] using hbase
+    simpa only [neg_neg, Function.comp_def] using hbase
   have hden :
       Tendsto (fun a : ℕ => B * (a : ℝ) ^ sigma) atTop (nhds 0) :=
     by simpa using (tendsto_const_nhds.mul hpow :
```

## PRPKG24AccuracyDiversity/AppendixD1GenericIV.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/AppendixD1GenericIV.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/AppendixD1GenericIV.lean
@@ -599,7 +599,8 @@
   have htarget_eq := sourcePowerObjective_eq_weightedPowerObjective
     p hsigma_lt_one hp_pos (targetShare p sigma)
   rw [hx_eq, htarget_eq]
-  simpa [targetShare] using htarget
+  unfold targetShare targetWeight
+  simpa only [one_mul] using htarget
 
 /--
 The continuous corrected objective has a strict gap away from its target.
@@ -635,7 +636,8 @@
     intro z hz hsum
     have hmax := weightedPowerObjective_target_maximizes
       w hsigma_pos hsigma_lt_one hw_pos z hz hsum
-    simpa [GeneralRounding.objective, weightedPowerObjective, g, q] using hmax
+    simp only [one_mul] at hmax
+    exact hmax
   have hstrict := GeneralRounding.objective_lt_of_ne_of_strictConcave_maximizer
     g 1 q x hconc hq_nonneg hq_sum hq_opt hx_nonneg hx_sum (by
       intro h
@@ -712,7 +714,8 @@
       simpa [bAlloc, AppliedModelingLib.Allocation.total] using hb
     have h := powerBenchmarkAllocation_optimal p sigma N bAlloc hbtotal
     simpa [bAlloc, AppliedModelingLib.Allocation.objective, sourcePowerObjective] using h
-  simpa [targetShare, Fintype.card_fin] using
+  unfold targetShare targetWeight
+  simpa only [Fintype.card_fin] using
     lemmaD1_iv_exactPower_integer_maximizer_rounding_window
       p hsigma_pos hsigma_lt_one hp_pos N
       (fun i => (powerBenchmarkAllocation p sigma N).count i) hsum hopt
```

## PRPKG24AccuracyDiversity/AppendixD3Source.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/AppendixD3Source.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/AppendixD3Source.lean
@@ -71,7 +71,7 @@
         AppliedModelingLib.Probability.sampleTopKSum sample k) =ᵐ[M.iidProductMeasure q]
         exponentialFiniteSampleTopKSum (q := q) k := by
     filter_upwards [M.iidProductMeasure_all_nonnegative_ae q] with sample hnonneg
-    simpa [exponentialFiniteSampleTopKSum] using
+    exact
       (AppliedModelingLib.Probability.topKSumOn_eq_sampleTopKSum_of_forall_nonneg
         sample k hnonneg).symm
   exact (exponentialFiniteSampleTopKSum_integrable M k).congr hsample_eq.symm
@@ -143,7 +143,7 @@
     AppliedModelingLib.Probability.expectedSampleTopKSum (M.iidProductMeasure q) k =
         ∫ sample, exponentialFiniteSampleTopKSum (q := q) k sample
           ∂M.iidProductMeasure q := by
-          simpa [exponentialFiniteSampleTopKSum] using
+          exact
             (AppliedModelingLib.Probability.expectedSampleTopKSum_eq_integral_topKSumOn_of_ae_nonneg
               (M.iidProductMeasure q) k (M.iidProductMeasure_all_nonnegative_ae q))
     _ = exponentialTopKOrderStatisticValue lambda k q := by
@@ -175,7 +175,7 @@
         AppliedModelingLib.Probability.expectedUpperOrderStatistic
           ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
           ⟨r, hrq⟩ := by
-          simpa [expectedOrderStatisticMeanSeq] using
+          exact
             AppliedModelingLib.Probability.expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
               (μ := (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
               (r := r) (a := q) hrq
```

## PRPKG24AccuracyDiversity/ContinuousSphereConcrete.lean

```diff
--- upstream/PRPKG24AccuracyDiversity/ContinuousSphereConcrete.lean
+++ lean-4.34.1/PRPKG24AccuracyDiversity/ContinuousSphereConcrete.lean
@@ -217,7 +217,7 @@
       (sphereUniformMeasure μ) (sphereUniformMeasure μ) := by
   refine ⟨(linearIsometrySphereAction_measurableEmbedding g).measurable, ?_⟩
   unfold sphereUniformMeasure
-  rw [MeasureTheory.Measure.map_smul,
+  rw [MeasureTheory.Measure.map_smul _ (linearIsometrySphereAction_measurableEmbedding g).measurable.aemeasurable,
     (sphereSurfaceMeasure_measurePreserving_linearIsometrySphereAction
       μ g hμ).map_eq]
 
@@ -794,7 +794,7 @@
   have hkernel_swap :
       Continuous
         (Function.uncurry (logRadialDistanceKernel (E := E) p)) := by
-    simpa [Function.uncurry] using
+    exact
       hkernel.comp (continuous_snd.prodMk continuous_fst)
   have hkernel_integrable :
       MeasureTheory.Integrable
@@ -814,7 +814,7 @@
         (MeasureTheory.volume : MeasureTheory.Measure E))
       (f := logRadialDistanceKernel (E := E) p)
       hkernel_integrable
-  simpa [logRadialDistanceProfilePayoff] using hswap.symm
+  exact hswap.symm
 
 /--
 Equations (23)--(24): after the Fubini swap, sphere symmetry makes the inner
@@ -1039,7 +1039,7 @@
         ∂sphereUniformMeasure (MeasureTheory.volume : MeasureTheory.Measure E))
       ?_ ?_ ?_ hpayoff_bddAbove
   · intro alpha
-    simpa [logRadialDistanceProfilePayoff] using
+    exact
       (kernel_integrable_uniform alpha).integral_prod_right
   · intro alpha
     calc
@@ -1056,7 +1056,7 @@
                   (MeasureTheory.volume : MeasureTheory.Measure E))
                 (f := logRadialDistanceKernel (E := E) p)
                 (kernel_integrable_uniform alpha)
-            simpa [logRadialDistanceProfilePayoff] using hswap.symm
+            exact hswap.symm
       _ = ∫ _x : UnitSphere E,
             (∫ u, logRadialDistanceKernel p anchor u
               ∂sphereUniformMeasure
@@ -1446,7 +1446,7 @@
     have hkernel_swap :
         Continuous
           (Function.uncurry (logRadialDistanceKernel (E := E) p)) := by
-      simpa [Function.uncurry] using
+      exact
         hkernel.comp (continuous_snd.prodMk continuous_fst)
     exact
       continuous_integrable_of_probability_compact
```
