# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

The following exact diffs retain the recorded compatibility choices. Source hash and import-relocation checks do not prove global equivalence of the historical and modern library environments.

## EconCSLib/Foundations/Math/FiniteSum.lean

```diff
--- upstream/EconCSLib/Foundations/Math/FiniteSum.lean
+++ lean-4.34.1/EconCSLib/Foundations/Math/FiniteSum.lean
@@ -1,3 +1,4 @@
+import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
 import Mathlib.Algebra.BigOperators.Group.Finset.Basic
 import Mathlib.Algebra.BigOperators.Group.List.Basic
 import Mathlib.Algebra.BigOperators.Fin
@@ -286,13 +287,13 @@
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

## EconCSLib/Foundations/Math/FiniteOptimization.lean

```diff
--- upstream/EconCSLib/Foundations/Math/FiniteOptimization.lean
+++ lean-4.34.1/EconCSLib/Foundations/Math/FiniteOptimization.lean
@@ -47,10 +47,8 @@
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

## EconCSLib/Foundations/Math/Asymptotics.lean

```diff
--- upstream/EconCSLib/Foundations/Math/Asymptotics.lean
+++ lean-4.34.1/EconCSLib/Foundations/Math/Asymptotics.lean
@@ -1376,7 +1376,7 @@
       Tendsto
         (fun N : ℕ => Real.log (1 - (1 : ℝ) / (((N + 1 : ℕ) : ℝ))))
         atTop (nhds 0) := by
-    simpa [Real.log_one] using
+    simpa only [Function.comp_def, Real.log_one] using
       (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
   simpa using hlog.neg
```

## EconCSLib/Foundations/Probability/FiniteSupportMGF.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/FiniteSupportMGF.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/FiniteSupportMGF.lean
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
@@ -1378,7 +1377,7 @@
       Filter.Tendsto (fun z : ℝ => finiteLogMGF μ score z)
         Filter.atBot
         (nhds (Real.log pZero)) := by
-    simpa [finiteLogMGF] using
+    simpa only [finiteLogMGF, Function.comp_def] using
       (Real.continuousAt_log (ne_of_gt hpZero_pos)).tendsto.comp hmgf
   have hneg :
       Filter.Tendsto (fun z : ℝ => -finiteLogMGF μ score z)
```

## EconCSLib/Foundations/Math/EpsilonContinuity.lean

```diff
--- upstream/EconCSLib/Foundations/Math/EpsilonContinuity.lean
+++ lean-4.34.1/EconCSLib/Foundations/Math/EpsilonContinuity.lean
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

## EconCSLib/Foundations/Probability/LargeDeviations.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/LargeDeviations.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/LargeDeviations.lean
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

## EconCSLib/Foundations/Math/BinomialBounds.lean

```diff
--- upstream/EconCSLib/Foundations/Math/BinomialBounds.lean
+++ lean-4.34.1/EconCSLib/Foundations/Math/BinomialBounds.lean
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

## EconCSLib/Foundations/Probability/IIDLargeDeviations.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/IIDLargeDeviations.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/IIDLargeDeviations.lean
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

## EconCSLib/Foundations/Probability/FiniteProductMultinomialCounts.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/FiniteProductMultinomialCounts.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/FiniteProductMultinomialCounts.lean
@@ -1,3 +1,4 @@
+import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
 import EconCSLib.Foundations.Probability.IIDLargeDeviations
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

## EconCSLib/Foundations/Probability/FiniteEmpiricalMultinomialCounts.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/FiniteEmpiricalMultinomialCounts.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/FiniteEmpiricalMultinomialCounts.lean
@@ -1,3 +1,4 @@
+import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
 import EconCSLib.Foundations.Math.SimplexRounding
 import EconCSLib.Foundations.Probability.FiniteProductMultinomialCounts
 
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

## EconCSLib/Foundations/Probability/FiniteRatingComparison.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/FiniteRatingComparison.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/FiniteRatingComparison.lean
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
         (EconCSLib.pmfExp (M.typeLaw hi) M.score) 0 := by
-    simpa [FiniteRatingLDPModel.logMGF] using
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using
       finiteLogMGF_hasDerivAt_zero (M.typeLaw hi) M.score
   have hderiv_lo :
       HasDerivAt (fun t : ℝ => M.logMGF lo t)
         (EconCSLib.pmfExp (M.typeLaw lo) M.score) 0 := by
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
         (EconCSLib.pmfExp (M.typeLaw hi) M.score)
@@ -1045,7 +1044,7 @@
         zHi := by
     have hformula := finiteLogMGF_hasDerivAt (M.typeLaw hi) M.score zHi
     rw [pmfExp_finiteExponentialTilt_eq]
-    simpa [FiniteRatingLDPModel.logMGF] using hformula
+    simpa only [FiniteRatingLDPModel.logMGF, Function.comp_def] using hformula
   have hderiv_lo :
       HasDerivAt (fun t : ℝ => M.logMGF lo t)
         (EconCSLib.pmfExp
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

## EconCSLib/Foundations/Probability/BinaryRatingLDP.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/BinaryRatingLDP.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/BinaryRatingLDP.lean
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
@@ -5467,7 +5463,8 @@
       ((realBernoulliPMF (successProb x) (hprob0 x) (hprob1 x) b).toReal :
         ℝ) := by
   cases b
-  · simpa using (measurable_const.sub hprob_meas)
+  · have h : Measurable (fun x => (1 : ℝ) - successProb x) := measurable_const.sub hprob_meas
+    simpa only [realBernoulliPMF_apply_false_toReal] using h
   · simpa using hprob_meas
 
 /--
```

## GJ19OptimalBinaryRatingSystems/MainTheorems.lean

```diff
--- upstream/GJ19OptimalBinaryRatingSystems/MainTheorems.lean
+++ lean-4.34.1/GJ19OptimalBinaryRatingSystems/MainTheorems.lean
@@ -1747,7 +1747,7 @@
     rw [binaryEndpointAwareAdjacentRate_first levels sampleRate i hfirst,
       binaryEndpointAwareAdjacentRate_first levels
         (fun _ : Fin (m + 2) ↦ (1 : ℝ)) i hfirst]
-    simpa [gLast] using mul_le_mul_of_nonneg_right hlocal_le hlog_nonneg
+    convert! mul_le_mul_of_nonneg_right hlocal_le hlog_nonneg using 1 <;> simp [gLast, lastLow, adjacentLowIndex, lastAdjacentIndex, Fin.castSucc, Fin.castAdd] <;> rfl
   · by_cases hlast : i.val = m
     · have hi : adjacentLowIndex i = lastLow := by
         ext
@@ -2812,7 +2812,7 @@
   have hpHi1 : oldLevels ⟨k + 1, by omega⟩ ≤ 1 :=
     BinaryEndpointLevelVector_le_one hold ⟨k + 1, by omega⟩
   have hlt : oldLevels ⟨k, by omega⟩ < oldLevels ⟨k + 1, by omega⟩ := by
-    simpa [adjacentLowIndex, adjacentHighIndex] using
+    exact
       hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
   have hmem :=
     bernoulliInteriorEqualSplit_mem_Ioo hpLo0 hpHi1 hlt
@@ -3255,7 +3255,7 @@
         BinaryEndpointLevelVector_le_one hold ⟨k + 1, by omega⟩
       have hlt : oldLevels (⟨k, by omega⟩ : Fin (m + 2)) <
           oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2)) := by
-        simpa [adjacentLowIndex, adjacentHighIndex] using
+        exact
           hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
       have hmem :=
         bernoulliInteriorEqualSplit_mem_Ioo hpLo0 hpHi1 hlt
@@ -3322,7 +3322,7 @@
         BinaryEndpointLevelVector_le_one hold ⟨k + 1, by omega⟩
       have hlt : oldLevels (⟨k, by omega⟩ : Fin (m + 2)) <
           oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2)) := by
-        simpa [adjacentLowIndex, adjacentHighIndex] using
+        exact
           hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
       have hmem :=
         bernoulliInteriorEqualSplit_mem_Ioo hpLo0 hpHi1 hlt
@@ -3353,7 +3353,7 @@
   · have hcopy :=
       uniformDoubledEndpointLevels_even oldLevels
         (lastLevelIndex : Fin (m + 2))
-    simpa [lastLevelIndex] using hcopy.trans hold.2.1
+    simpa [lastLevelIndex, Nat.mul_add, Nat.add_assoc] using hcopy.trans hold.2.1
   · intro i
     by_cases hEven : i.val % 2 = 0
     · let k := i.val / 2
@@ -3543,7 +3543,7 @@
               omega)
       have hlt : pLo < pHi := by
         dsimp [pLo, pHi]
-        simpa [adjacentLowIndex, adjacentHighIndex] using
+        exact
           hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
       have hrate :=
         weightedBernoulliClosedThresholdRate_one_one_interiorEqualSplit_left_eq_transform
@@ -3619,7 +3619,7 @@
         BinaryEndpointLevelVector_le_one hold ⟨k + 1, by omega⟩
       have hlt : oldLevels (⟨k, by omega⟩ : Fin (m + 2)) <
           oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2)) := by
-        simpa [adjacentLowIndex, adjacentHighIndex] using
+        exact
           hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
       have hrate :=
         lemmaC5_uniform_interiorEqualSplit_rate_eq hpLo0 hpHi1 hlt
@@ -3899,8 +3899,8 @@
       Filter.Tendsto (fun r : ℝ => Real.exp (-(r / g)))
         Filter.atTop (nhds 0) :=
     Real.tendsto_exp_atBot.comp hlin
-  simpa [binaryEndpointFirstLevelOfRate] using
-    (tendsto_const_nhds (x := (1 : ℝ))).sub hexp
+  unfold binaryEndpointFirstLevelOfRate
+  convert! (tendsto_const_nhds (x := (1 : ℝ))).sub hexp using 1 <;> simp <;> rfl
 
 /-- The last endpoint inverse tends to the lower endpoint as the target rate grows. -/
 theorem binaryEndpointLastLevelOfRate_tendsto_atTop
@@ -3923,8 +3923,8 @@
     ext r
     field_simp [hg_ne]
     ring
-  simpa [binaryEndpointLastLevelOfRate] using
-    Real.tendsto_exp_atBot.comp hlin
+  unfold binaryEndpointLastLevelOfRate
+  convert! Real.tendsto_exp_atBot.comp hlin using 1 <;> rfl
 
 /-- The first endpoint rate is strictly increasing in the endpoint level. -/
 theorem binaryEndpointFirstRate_strictMonoOn
@@ -4058,16 +4058,15 @@
         r :=
     (binaryEndpointLastLevelOfRate_continuous gHi).continuousAt.prodMk
       (binaryEndpointFirstLevelOfRate_continuous gLo).continuousAt
-  simpa [binaryEndpointTwoInteriorMiddleRate, pHi, pLo] using
-    hclosed.comp_of_eq hpair (by rfl)
+  unfold binaryEndpointTwoInteriorMiddleRate
+  convert! hclosed.comp_of_eq hpair (by rfl) using 1 <;> rfl
 
 /-- The two-interior-level scalar target-rate gap is continuous at positive rates. -/
 theorem binaryEndpointTwoInteriorMiddleRateGap_continuousAt
     {gLo gHi r : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) (hr : 0 < r) :
     ContinuousAt (binaryEndpointTwoInteriorMiddleRateGap gLo gHi) r := by
-  simpa [binaryEndpointTwoInteriorMiddleRateGap] using
-    (binaryEndpointTwoInteriorMiddleRate_continuousAt
-      hgLo hgHi hr).sub continuousAt_id
+  unfold binaryEndpointTwoInteriorMiddleRateGap
+  convert! (binaryEndpointTwoInteriorMiddleRate_continuousAt hgLo hgHi hr).sub continuousAt_id using 1 <;> rfl
 
 /--
 The two-interior scalar target-rate gap is continuous on the positive-rate
@@ -4116,8 +4115,7 @@
       have hcont :
           ContinuousAt (binaryEndpointFirstLevelOfRate gLo) (0 : ℝ) :=
         (binaryEndpointFirstLevelOfRate_continuous gLo).continuousAt
-      simpa [binaryEndpointFirstLevelOfRate] using
-        hcont.tendsto.mono_left nhdsWithin_le_nhds
+      convert! hcont.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> simp [binaryEndpointFirstLevelOfRate] <;> rfl
   have hlast :
       Filter.Tendsto (binaryEndpointLastLevelOfRate gHi)
         (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) :=
@@ -4125,8 +4123,7 @@
       have hcont :
           ContinuousAt (binaryEndpointLastLevelOfRate gHi) (0 : ℝ) :=
         (binaryEndpointLastLevelOfRate_continuous gHi).continuousAt
-      simpa [binaryEndpointLastLevelOfRate] using
-        hcont.tendsto.mono_left nhdsWithin_le_nhds
+      convert! hcont.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> simp [binaryEndpointLastLevelOfRate] <;> rfl
   have hfailLo :
       Filter.Tendsto
         (fun r : ℝ => (1 - binaryEndpointFirstLevelOfRate gLo r) ^ aLo)
@@ -4327,7 +4324,8 @@
     binaryEndpointFirstLevelOfRate_tendsto_atTop (g := gFirst) hgFirst
   have hlast :=
     binaryEndpointLastLevelOfRate_tendsto_atTop (g := gLast) hgLast
-  simpa [binaryEndpointInverseGap] using hfirst.sub hlast
+  unfold binaryEndpointInverseGap
+  convert! hfirst.sub hlast using 1 <;> simp <;> rfl
 
 /-- The endpoint inverse gap is positive somewhere for positive endpoint weights. -/
 theorem binaryEndpointInverseGap_exists_pos
@@ -4975,8 +4973,7 @@
     have hcontinuous :
         ContinuousAt (binaryEndpointLastLevelOfRate gLast) (0 : ℝ) :=
       (binaryEndpointLastLevelOfRate_continuous gLast).continuousAt
-    simpa [gLast, binaryEndpointLastLevelOfRate] using
-      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
+    convert! hcontinuous.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> simp [gLast, binaryEndpointLastLevelOfRate] <;> rfl
   convert hcont using 1
   ext r
   simp [binaryEndpointForwardClippedCap, gLast,
@@ -5023,8 +5020,7 @@
                     (binaryEndpointSampleRateNat sampleRate 1)) (0 : ℝ) :=
               (binaryEndpointFirstLevelOfRate_continuous
                 (binaryEndpointSampleRateNat sampleRate 1)).continuousAt
-            simpa [binaryEndpointFirstLevelOfRate] using
-              hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
+            convert! hcontinuous.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> simp [binaryEndpointFirstLevelOfRate] <;> rfl
           have hcap_tendsto :=
             binaryEndpointForwardClippedCap_tendsto_nhdsGT_zero sampleRate
           have hfirst_lt_half :
@@ -5760,7 +5756,7 @@
   intro i
   have hraw := hsample_pos (i.val + 1) (by omega)
   rw [binaryEndpointSampleRateNat_of_lt sampleRate (by omega)] at hraw
-  simpa [adjacentHighIndex] using hraw
+  exact hraw
 
 /-- Convert support-safe natural-index positivity to adjacent-low positivity. -/
 theorem binaryEndpointSampleRateNat_pos_adjacentLow {m : ℕ}
@@ -5771,7 +5767,7 @@
   intro i
   have hraw := hsample_pos i.val (by omega)
   rw [binaryEndpointSampleRateNat_of_lt sampleRate (by omega)] at hraw
-  simpa [adjacentLowIndex] using hraw
+  exact hraw
 
 @[simp] theorem binaryEndpointForwardClippedLevelNat_zero {m : ℕ}
     (sampleRate : Fin (m + 2) → ℝ) (cap r : ℝ) :
@@ -9241,13 +9237,13 @@
     intro i
     have hraw := hsample_pos (i.val + 1) (by omega)
     rw [binaryEndpointSampleRateNat_of_lt sampleRate (by omega)] at hraw
-    simpa [adjacentHighIndex] using hraw
+    exact hraw
   have hsample_low :
       ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i) := by
     intro i
     have hraw := hsample_pos i.val (by omega)
     rw [binaryEndpointSampleRateNat_of_lt sampleRate (by omega)] at hraw
-    simpa [adjacentLowIndex] using hraw
+    exact hraw
   rcases
     binaryEndpointInverseGap_existsUnique_pos_zero_and_nonneg_iff
       (hsample_pos 1 (by omega)) (hsample_pos m (by omega)) with
@@ -13766,7 +13762,7 @@
         0 ≤
           ∫ x in P.pieceSet component, weight x ∂(μ.prod μ) := by
     intro component
-    exact setIntegral_nonneg_of_ae_restrict (by simpa [P] using hweight_nonneg component)
+    exact setIntegral_nonneg_of_ae_restrict (by exact hweight_nonneg component)
   have hweight_pos_integral :
       0 <
         ∫ x in P.pieceSet (theorem31OrderedAdjacentPiece hm minAdjacent),
```

## GJ19OptimalBinaryRatingSystems/ContinuumTheorems.lean

```diff
--- upstream/GJ19OptimalBinaryRatingSystems/ContinuumTheorems.lean
+++ lean-4.34.1/GJ19OptimalBinaryRatingSystems/ContinuumTheorems.lean
@@ -779,7 +779,7 @@
     · simpa [canonicalUniformEqualizedEndpointLevels,
         canonicalTinyEndpointLevels, firstLevelIndex] using hoptimal.1.1
     · simpa [canonicalUniformEqualizedEndpointLevels,
-        canonicalTinyEndpointLevels] using hoptimal.1.2.1
+        canonicalTinyEndpointLevels, lastLevelIndex, Fin.last] using hoptimal.1.2.1
 
 /--
 Lemma C.4 reverse-branch obstruction.  The source's non-piecewise argument
@@ -9996,7 +9996,7 @@
     (μ : Measure ℝ) [SFinite μ] :
     MeasurePreserving theorem31SelectedSourceCoordinateMap (μ.prod μ)
       (μ.prod μ) := by
-  simpa [theorem31SelectedSourceCoordinateMap] using
+  exact
     (MeasureTheory.Measure.measurePreserving_swap (μ := μ) (ν := μ))
 
 /-- The selected finite-level source support is measurable. -/
@@ -10040,13 +10040,13 @@
       q.2 ∈ Set.Ioc (cut piece.val.1.val) (cut (piece.val.1.val + 1)) := by
     simpa [theorem31SelectedSourceCoordinateMap,
       theorem31_ordered_quality_interval_partition,
-      FiniteMeasurableSetPartition.orderedRealIocNatCutpoints] using
+      FiniteMeasurableSetPartition.orderedRealIocNatCutpoints, MeasurableEquiv.prodComm] using
       hprod.1
   have hhigh :
       q.1 ∈ Set.Ioc (cut piece.val.2.val) (cut (piece.val.2.val + 1)) := by
     simpa [theorem31SelectedSourceCoordinateMap,
       theorem31_ordered_quality_interval_partition,
-      FiniteMeasurableSetPartition.orderedRealIocNatCutpoints] using
+      FiniteMeasurableSetPartition.orderedRealIocNatCutpoints, MeasurableEquiv.prodComm] using
       hprod.2
   have hindex : piece.val.1.val + 1 ≤ piece.val.2.val :=
     piece.property.1
```

## GJ19OptimalBinaryRatingSystems/Theorem32Appendix.lean

```diff
--- upstream/GJ19OptimalBinaryRatingSystems/Theorem32Appendix.lean
+++ lean-4.34.1/GJ19OptimalBinaryRatingSystems/Theorem32Appendix.lean
@@ -3293,7 +3293,9 @@
               (adjacentLowIndex (firstAdjacentIndex : Fin (n + 1))) = 0 := by
         simp [returned, theorem32WeightedBackwardLowBisectionLevels,
           adjacentLowIndex, firstAdjacentIndex]
-      simpa [returned, hlow] using hfirst_pos
+      change returned (adjacentLowIndex firstAdjacentIndex) < returned (adjacentHighIndex firstAdjacentIndex)
+      rw [hlow]
+      exact hfirst_pos
     · by_cases hlast : i.val = n
       · have hi : i = (lastAdjacentIndex : Fin (n + 1)) := by
           ext
@@ -4315,7 +4317,7 @@
     have hnot_first :
         (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))).val ≠ 0 := by
       simp [adjacentHighIndex, firstAdjacentIndex]
-    simpa [tFirst] using
+    exact
       BinaryEndpointLevelVector_pos_of_not_first hoptimal_levels
         (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) hnot_first
   have htarget_pos : 0 < target := by
@@ -5450,7 +5452,9 @@
               (adjacentLowIndex (firstAdjacentIndex : Fin (n + 1))) = 0 := by
         simp [returned, theorem32WeightedBackwardGridRateBisectionLevels,
           adjacentLowIndex, firstAdjacentIndex]
-      simpa [returned, hlow] using hfirst_pos
+      change returned (adjacentLowIndex firstAdjacentIndex) < returned (adjacentHighIndex firstAdjacentIndex)
+      rw [hlow]
+      exact hfirst_pos
     · by_cases hi_last : i.val = n
       · have hi : i = (lastAdjacentIndex : Fin (n + 1)) := by
           ext
@@ -5478,7 +5482,7 @@
         rw [hlow, hhigh]
         exact hlastLow_lt_one
       · have hlow_pos : 0 < returned (adjacentLowIndex i) := by
-          simpa [returned, adjacentLowIndex] using
+          exact
             theorem32WeightedBackwardGridRateBisectionLevels_pos_of_first_high_pos
               hn sampleRate grid target lastLow hgrid_pos hfirst_pos
               i.val (Nat.pos_of_ne_zero hi_first) (Nat.le_of_lt_succ i.2)
@@ -5981,7 +5985,7 @@
     ext
     exact hval
   have h := hstep (n - i.val) hd_pos hd_lt
-  simpa [returned, target, gLast, hi_eq] using h
+  convert! h using 1 <;> simp [returned, target, gLast, hi_eq] <;> rfl
 
 /--
 Source outer-branch shifting consequence.  Once the tested final-low endpoint
@@ -6742,7 +6746,7 @@
         binaryEndpointAwareAdjacentRate_last_lt_of_low_lt
           hm_pos sampleRate returned optimal hreturnedLevels hoptimalLevels
           (hsample_pos (adjacentLowIndex last))
-          (by simpa [lastLow] using hleft)
+          (by exact hleft)
     have hfirst_rate_lt :
         binaryEndpointAwareAdjacentRate optimal sampleRate first <
           binaryEndpointAwareAdjacentRate returned sampleRate first := by
@@ -7772,7 +7776,7 @@
     have hsource_upper_pos :
         0 < returned (adjacentHighIndex i) - grid :=
       htFirst_pos.trans_le
-        (by simpa [returned, tFirst] using
+        (by exact
           hfloor_le_grid_upper i hi_first hi_last)
     have hsample_high_le : sampleRate (adjacentHighIndex i) ≤ gLast := by
       dsimp [gLast, last]
@@ -7816,7 +7820,7 @@
           (sampleRate (adjacentHighIndex i))
           (sampleRate (adjacentLowIndex i))
           (returned (adjacentHighIndex i)) (root i) = target := by
-        simpa [root, returned, tFirst, target] using
+        exact
           weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible
             (hinner_feasible i hi_first hi_last)
       _ = binaryEndpointAwareAdjacentRate returned sampleRate last :=
@@ -7956,7 +7960,7 @@
       (rStar := rStar) (gLast := gLast) (delta := grid) (eps := eps)
       hgLast_pos heps hoptimalLevels heq hsample_pos hsample_mono
       hfirst_sample hlast_width
-      (by simpa [gLast] using hgrid_choice)
+      (by exact hgrid_choice)
       hoptimal_rates hlastLoss hinnerGrid houterSteps hinnerSteps
 
 /--
@@ -8228,7 +8232,9 @@
               (adjacentLowIndex (firstAdjacentIndex : Fin (n + 1))) = 0 := by
         simp [returned, theorem32BackwardLowBisectionLevels,
           adjacentLowIndex, firstAdjacentIndex]
-      simpa [returned, hlow] using hfirst_pos
+      change returned (adjacentLowIndex firstAdjacentIndex) < returned (adjacentHighIndex firstAdjacentIndex)
+      rw [hlow]
+      exact hfirst_pos
     · by_cases hlast : i.val = n
       · have hi : i = (lastAdjacentIndex : Fin (n + 1)) := by
           ext
@@ -8617,7 +8623,9 @@
               (adjacentLowIndex (firstAdjacentIndex : Fin (n + 1))) = 0 := by
         simp [returned, theorem32BackwardGridLowBisectionLevels,
           adjacentLowIndex, firstAdjacentIndex]
-      simpa [returned, hlow] using hfirst_pos
+      change returned (adjacentLowIndex firstAdjacentIndex) < returned (adjacentHighIndex firstAdjacentIndex)
+      rw [hlow]
+      exact hfirst_pos
     · by_cases hlast : i.val = n
       · have hi : i = (lastAdjacentIndex : Fin (n + 1)) := by
           ext
@@ -8936,7 +8944,9 @@
           theorem32BackwardGridLowBisectionLevels_first_high_pos_of_root_le_grid_upper
             (n := n) (innerSteps := innerSteps) hn grid tFirst target lastLow
             htFirst_pos hroot_le_grid_upper
-      simpa [returned, hlow] using hfirst_pos
+      change returned (adjacentLowIndex firstAdjacentIndex) < returned (adjacentHighIndex firstAdjacentIndex)
+      rw [hlow]
+      exact hfirst_pos
     · by_cases hlast : i.val = n
       · have hi : i = (lastAdjacentIndex : Fin (n + 1)) := by
           ext
@@ -13336,7 +13346,7 @@
       hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
       hfirstRate root lower hroot0 htFirst_le_root hroot_rate hbracket
       houter hinner
-  simpa [run] using
+  exact
     binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
       (m := m) (M := M) (L := L)
       hm oldLevels returned heps holdLevels holdEq run
@@ -13437,7 +13447,7 @@
       hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
       hfirstRate root lower0 upper0 hroot0 htFirst_le_root hroot_rate
       hinnerLower0 hinnerUpper0 hinnerWidth hreturnedLow houter hinner
-  simpa [run] using
+  exact
     binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
       (m := m) (M := M) (L := L)
       hm oldLevels returned heps holdLevels holdEq run
@@ -13565,7 +13575,7 @@
       hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
       hfirstRate lower0 upper0 hfeasible hinnerLower0 hinnerUpper0
       hinnerWidth hreturnedLow houter hinner
-  simpa [run] using
+  exact
     binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
       (m := m) (M := M) (L := L)
       hm oldLevels returned heps holdLevels holdEq run
@@ -13717,7 +13727,7 @@
       hlevelAbove hlevelBelow hlevelLower0 hlevelUpper0 hlevelWidth
       hreturnedLast hfirst_ge hlast_ge hfeasible
       hinnerLower0 hinnerUpper0 hinnerWidth hreturnedLow houter hinner
-  simpa [run] using
+  exact
     binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
       (m := m) (M := M) (L := L)
       hm oldLevels returned heps holdLevels holdEq run
@@ -14196,7 +14206,7 @@
       uniformDoubledEndpointLevels oldLevels
           (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
           root firstInterior := by
-            simpa [tFirst] using hroot_mem.1.le
+            exact hroot_mem.1.le
       _ ≤ returned (adjacentLowIndex firstInterior) := hroot_le_returned
       _ =
           returned
@@ -15998,7 +16008,7 @@
   have hfirst_root_mem :
       root firstInterior ∈
         Set.Ioo tFirst (returned (adjacentHighIndex firstInterior)) := by
-    simpa [root, returned, tFirst, target] using
+    exact
       weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
         (hfeasible firstInterior hfirstInterior_not_first
           hfirstInterior_not_last)
@@ -16008,7 +16018,7 @@
   have hfirst_root_le_grid_upper :
       root firstInterior ≤
         returned (adjacentHighIndex firstInterior) - grid := by
-    simpa [root, returned, tFirst, target] using
+    exact
       hroot_le_grid_upper firstInterior hfirstInterior_not_first
         hfirstInterior_not_last
   have hfirst_run_target_le :
@@ -16043,7 +16053,7 @@
       uniformDoubledEndpointLevels oldLevels
           (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
           root firstInterior := by
-            simpa [tFirst] using hfirst_root_mem.1.le
+            exact hfirst_root_mem.1.le
       _ ≤ returned (adjacentLowIndex firstInterior) := by
             simpa [hfirst_returned_low] using hfirst_run_target_le
       _ =
@@ -16086,7 +16096,7 @@
         intro i hi_first hi_last
         have hmem :
             root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
-          simpa [root, returned, tFirst, target] using
+          exact
             weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
               (hfeasible i hi_first hi_last)
         exact le_of_lt ((hfeasible i hi_first hi_last).hfloor0.trans hmem.1))
@@ -16225,7 +16235,7 @@
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
           0 := by
       simp [adjacentHighIndex, firstAdjacentIndex]
-    simpa [tFirst] using
+    exact
       BinaryEndpointLevelVector_pos_of_not_first
         hoptimalLevels
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
@@ -16354,7 +16364,7 @@
           (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
           root i := by
     intro i hi_first hi_last
-    simpa [tFirst] using
+    exact
       (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
         (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
         (pHi := returned (adjacentHighIndex i)) (target := target))
@@ -16367,7 +16377,7 @@
   have hfirst_root_le_grid_upper :
       root firstInterior ≤
         returned (adjacentHighIndex firstInterior) - grid := by
-    simpa [root, returned, tFirst, target] using
+    exact
       hroot_le_grid_upper firstInterior hfirstInterior_not_first
         hfirstInterior_not_last
   have hfirst_run_target_le :
@@ -16449,7 +16459,7 @@
     intro i hi_first hi_last
     have hroot_le :
         root i ≤ returned (adjacentHighIndex i) - grid := by
-      simpa [root, returned, tFirst, target] using
+      exact
         hroot_le_grid_upper i hi_first hi_last
     have hfloor_le_root : tFirst ≤ root i := by
       simpa [root] using
@@ -16522,7 +16532,7 @@
           outerSteps levelLower0 1).1)
       heps holdLevels holdEq hreturnedLevels
       (by
-        simpa [optimal, delta, hreturnedLast'] using hlastBracket)
+        have hCompatBracket := hlastBracket; rw [hreturnedLast'] at hCompatBracket; exact hCompatBracket)
       hfirstRate root
       (fun _ : Fin ((2 * m + 1) + 1) => (0 : ℝ))
       (fun i : Fin ((2 * m + 1) + 1) =>
@@ -16533,7 +16543,7 @@
         exact (hroot0 i hi_first hi_last).le)
       (by
         intro i hi_first hi_last
-        simpa [root, returned, tFirst, target] using
+        exact
           hroot_le_grid_upper i hi_first hi_last)
       hinnerWidth' hreturnedLow houter hinner
 
@@ -16659,7 +16669,7 @@
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
           0 := by
       simp [adjacentHighIndex, firstAdjacentIndex]
-    simpa [tFirst] using
+    exact
       BinaryEndpointLevelVector_pos_of_not_first
         hoptimalLevels
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
@@ -16748,7 +16758,7 @@
           (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
           root i := by
     intro i hi_first hi_last
-    simpa [tFirst] using
+    exact
       (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
         (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
         (pHi := returned (adjacentHighIndex i)) (target := target))
@@ -16761,7 +16771,7 @@
   have hfirst_root_le_grid_upper :
       root firstInterior ≤
         returned (adjacentHighIndex firstInterior) - grid := by
-    simpa [root, returned, tFirst, target] using
+    exact
       hroot_le_grid_upper firstInterior hfirstInterior_not_first
         hfirstInterior_not_last
   have hfirst_run_target_le :
@@ -16843,7 +16853,7 @@
     intro i hi_first hi_last
     have hroot_le :
         root i ≤ returned (adjacentHighIndex i) - grid := by
-      simpa [root, returned, tFirst, target] using
+      exact
         hroot_le_grid_upper i hi_first hi_last
     have hfloor_le_root : tFirst ≤ root i := by
       simpa [root] using
@@ -16924,7 +16934,7 @@
         exact (hroot0 i hi_first hi_last).le)
       (by
         intro i hi_first hi_last
-        simpa [root, returned, tFirst, target] using
+        exact
           hroot_le_grid_upper i hi_first hi_last)
       hinnerWidth' hreturnedLow houter hinner
 
@@ -17618,7 +17628,7 @@
   have hfirst_root_mem :
       root firstInterior ∈
         Set.Ioo tFirst (returned (adjacentHighIndex firstInterior)) := by
-    simpa [root, returned, tFirst, target] using
+    exact
       weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
         (hfeasible firstInterior hfirstInterior_not_first
           hfirstInterior_not_last)
@@ -17628,7 +17638,7 @@
   have hfirst_root_le_grid_upper :
       root firstInterior ≤
         returned (adjacentHighIndex firstInterior) - grid := by
-    simpa [root, returned, tFirst, target] using
+    exact
       hroot_le_grid_upper firstInterior hfirstInterior_not_first
         hfirstInterior_not_last
   have hfirst_run_target_le :
@@ -17663,7 +17673,7 @@
       uniformDoubledEndpointLevels oldLevels
           (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
           root firstInterior := by
-            simpa [tFirst] using hfirst_root_mem.1.le
+            exact hfirst_root_mem.1.le
       _ ≤ returned (adjacentLowIndex firstInterior) := by
             simpa [hfirst_returned_low] using hfirst_run_target_le
       _ =
@@ -17706,7 +17716,7 @@
         intro i hi_first hi_last
         have hmem :
             root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
-          simpa [root, returned, tFirst, target] using
+          exact
             weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
               (hfeasible i hi_first hi_last)
         exact le_of_lt ((hfeasible i hi_first hi_last).hfloor0.trans hmem.1))
@@ -17921,7 +17931,7 @@
     simpa [tFirst, target, returned] using
       (hfeasible i hi_first hi_last).htarget_lt_floor
   have htFirst_pos : 0 < tFirst := by
-    exact hgrid_pos.trans (by simpa [tFirst] using hgrid_lt_tFirst)
+    exact hgrid_pos.trans (by exact hgrid_lt_tFirst)
   have htFirst_lt_lastLow :
       let tFirst : ℝ :=
         uniformDoubledEndpointLevels oldLevels
@@ -17980,9 +17990,9 @@
       theorem32BackwardGridLowBisectionLevels_floor_lt_high_and_grid_upper_pos_of_grid_lt_floor
         (n := 2 * m + 1) (innerSteps := innerSteps)
         grid tFirst lastLow htFirst_pos hgrid_pos
-        (by simpa [tFirst] using hgrid_lt_tFirst)
+        (by exact hgrid_lt_tFirst)
         hlastLow_lt_one hlastLow_pos hlastLow_le_one_sub_grid
-        (by simpa [tFirst] using htFirst_lt_lastLow)
+        (by exact htFirst_lt_lastLow)
         (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
   have hgrid_upper_pos :
       let tFirst : ℝ :=
@@ -18440,7 +18450,7 @@
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
           0 := by
       simp [adjacentHighIndex, firstAdjacentIndex]
-    simpa [tFirst] using
+    exact
       BinaryEndpointLevelVector_pos_of_not_first
         hoptimalLevels
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
@@ -19587,13 +19597,13 @@
   have hlastLow_lt_one : lastLow < 1 := by
     linarith
   have htFirst_pos : 0 < tFirst :=
-    hgrid_pos.trans (by simpa [tFirst] using hgrid_lt_tFirst)
+    hgrid_pos.trans (by exact hgrid_lt_tFirst)
   have htFirst_lt_lastLow :
       let tFirst : ℝ :=
         uniformDoubledEndpointLevels oldLevels
           (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
       tFirst < lastLow := by
-    simpa [tFirst] using
+    exact
       theorem32_calculated_grid_tFirst_lt_lastLow_of_source_outer_return
         (m := m) (outerSteps := outerSteps)
         hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
@@ -19614,9 +19624,9 @@
       theorem32BackwardGridLowBisectionLevels_floor_lt_high_and_grid_upper_pos_of_grid_lt_floor
         (n := 2 * m + 1) (innerSteps := innerSteps)
         grid tFirst lastLow htFirst_pos hgrid_pos
-        (by simpa [tFirst] using hgrid_lt_tFirst)
+        (by exact hgrid_lt_tFirst)
         hlastLow_lt_one hlastLow_pos hlastLow_le_one_sub_grid
-        (by simpa [tFirst] using htFirst_lt_lastLow)
+        (by exact htFirst_lt_lastLow)
         (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
   have hfloor_lt_high :
       let tFirst : ℝ :=
@@ -23398,7 +23408,7 @@
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
           0 := by
       simp [adjacentHighIndex, firstAdjacentIndex]
-    simpa [tFirst] using
+    exact
       BinaryEndpointLevelVector_pos_of_not_first
         hoptimalLevels
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
@@ -23803,7 +23813,7 @@
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
           0 := by
       simp [adjacentHighIndex, firstAdjacentIndex]
-    simpa [tFirst] using
+    exact
       BinaryEndpointLevelVector_pos_of_not_first
         hoptimalLevels
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
@@ -23827,7 +23837,7 @@
         (n := 2 * m + 1) (innerSteps := innerSteps)
         grid tFirst lastLow htFirst_pos hgrid_pos hlastLow_lt_one
         hlastLow_pos hlastLow_le_one_sub_grid
-        (by simpa [tFirst] using htFirst_lt_lastLow)
+        (by exact htFirst_lt_lastLow)
         (by simpa [tFirst, target, returned] using hgrid_upper_pos)
         (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
   simpa [tFirst, target, returned] using
@@ -23935,7 +23945,7 @@
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
           0 := by
       simp [adjacentHighIndex, firstAdjacentIndex]
-    simpa [tFirst] using
+    exact
       BinaryEndpointLevelVector_pos_of_not_first
         hoptimalLevels
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
@@ -23960,9 +23970,9 @@
       theorem32BackwardGridLowBisectionLevels_floor_lt_high_and_grid_upper_pos_of_grid_lt_floor
         (n := 2 * m + 1) (innerSteps := innerSteps)
         grid tFirst lastLow htFirst_pos hgrid_pos
-        (by simpa [tFirst] using hgrid_lt_tFirst)
+        (by exact hgrid_lt_tFirst)
         hlastLow_lt_one hlastLow_pos hlastLow_le_one_sub_grid
-        (by simpa [tFirst] using htFirst_lt_lastLow)
+        (by exact htFirst_lt_lastLow)
         (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
   have hfloor_lt_high :
       let tFirst : ℝ :=
@@ -24352,7 +24362,7 @@
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
           0 := by
       simp [adjacentHighIndex, firstAdjacentIndex]
-    simpa [tFirst] using
+    exact
       BinaryEndpointLevelVector_pos_of_not_first
         hoptimalLevels
         (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
@@ -24378,7 +24388,7 @@
       hgLo := by norm_num
       hfloor0 := htFirst0
       hfloor_lt_hi := by
-        simpa [tFirst] using hfloor_lt_high i hi_first hi_last
+        exact hfloor_lt_high i hi_first hi_last
       hpHi1 := hhi_lt_one
       htarget_pos := htarget_pos
       htarget_lt_floor := by
@@ -25011,7 +25021,7 @@
       hm oldLevels returned rateLower0 rateUpper0 holdLevels
       hlevelLower0 hlevelUpper0 hlevelWidth hreturnedLast
       hinnerLower0 hinnerUpper0 hinnerWidth hreturnedRate houter hinner
-  simpa [run] using
+  exact
     binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
       (m := m) (M := M) (L := L)
       hm oldLevels returned heps holdLevels holdEq run
```

## EconCSLib/Foundations/Probability/MeasureInequalities.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/MeasureInequalities.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/MeasureInequalities.lean
@@ -962,7 +962,7 @@
 
 /-- Under a nonatomic measure, touching open intervals are equal a.e. -/
 theorem measure_symmDiff_Ioo_union_Ioo_touching_eq_zero
-    (μ : Measure ℝ) [NoAtoms μ]
+    (μ : Measure ℝ) [NullSingletonClass μ]
     {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
     μ ((Set.Ioo a b ∪ Set.Ioo b c) ∆ Set.Ioo a c) = 0 :=
   measure_mono_null
@@ -972,7 +972,7 @@
 
 /-- A.e. set equality form of `measure_symmDiff_Ioo_union_Ioo_touching_eq_zero`. -/
 theorem ae_eq_Ioo_union_Ioo_touching
-    (μ : Measure ℝ) [NoAtoms μ]
+    (μ : Measure ℝ) [NullSingletonClass μ]
     {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
     ((Set.Ioo a b ∪ Set.Ioo b c : Set ℝ) =ᵐ[μ] Set.Ioo a c) :=
   measure_symmDiff_eq_zero_iff.mp
@@ -1006,7 +1006,7 @@
 
 /-- Under a nonatomic measure, a touching open interval and right ray are equal a.e. -/
 theorem measure_symmDiff_Ioo_union_Ioi_touching_eq_zero
-    (μ : Measure ℝ) [NoAtoms μ]
+    (μ : Measure ℝ) [NullSingletonClass μ]
     {a b : ℝ} (hab : a ≤ b) :
     μ ((Set.Ioo a b ∪ Set.Ioi b) ∆ Set.Ioi a) = 0 :=
   measure_mono_null
@@ -1016,7 +1016,7 @@
 
 /-- A.e. set equality form of `measure_symmDiff_Ioo_union_Ioi_touching_eq_zero`. -/
 theorem ae_eq_Ioo_union_Ioi_touching
-    (μ : Measure ℝ) [NoAtoms μ]
+    (μ : Measure ℝ) [NullSingletonClass μ]
     {a b : ℝ} (hab : a ≤ b) :
     ((Set.Ioo a b ∪ Set.Ioi b : Set ℝ) =ᵐ[μ] Set.Ioi a) :=
   measure_symmDiff_eq_zero_iff.mp
@@ -1448,8 +1448,7 @@
     (hL1 := fun n =>
       (eLpNorm_le_eLpNorm_of_exponent_le
         (μ := μ) (f := S n)
-        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
-        ((hS.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable).trans
+        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
           (hL2 n))
 
 /--
@@ -1777,7 +1776,7 @@
   have hR_le_sq : max 1 S ≤ (max 1 S) ^ 2 := by
     nlinarith [hR_ge_one]
   have hS_le_sq : S ≤ (max 1 S) ^ 2 := le_trans hR_ge_S hR_le_sq
-  exact le_trans hpartial (by simpa [R] using hS_le_sq)
+  exact le_trans hpartial hS_le_sq
 
 /--
 Finite partial-sum second-moment induction with explicit cross-term control.
@@ -1951,7 +1950,7 @@
     exact
       (ENNReal.le_ofReal_iff_toReal_le
         (measure_ne_top μ (bad n)) (hbound_nonneg n)).2
-        (by simpa [Measure.real] using hle n)
+        (by simpa only [Measure.real, Function.comp_def] using hle n)
   have hsum_le :
       (∑' n, μ (bad n)) ≤ ∑' n, ENNReal.ofReal (bound n) :=
     ENNReal.tsum_le_tsum hterm
@@ -2061,7 +2060,7 @@
         (Ω := fun _ => Bool) (mΩ := fun _ => by infer_instance)
         (P := P) hμ (X := fun i : ι => (fun b : Bool => b))
         (mX := fun _ => measurable_id)
-  simpa [fairBoolProductMeasure, P] using hcoord.comp
+  simpa only [fairBoolProductMeasure, P, Function.comp_def] using hcoord.comp
     (fun _ b => if b = keep then (1 : ℝ) else 0)
     (fun _ => measurable_of_finite _)
 
@@ -2218,7 +2217,7 @@
   classical
   let ν : Measure ℝ := Measure.map z μ
   haveI : IsProbabilityMeasure ν :=
-    Measure.isProbabilityMeasure_map hz.aemeasurable
+    (by infer_instance)
   have hcdf :
       Filter.Tendsto (fun x : ℝ => ProbabilityTheory.cdf ν x)
         Filter.atBot (nhds 0) :=
@@ -2611,7 +2610,7 @@
       (fun q : ℝ =>
         (μ {p : ℝ × ℝ | p.1 ≤ a q ∧ b q ≤ p.2}).toReal)
       Filter.atBot (nhds (μ.real Set.univ))
-  simpa [Measure.real] using
+  simpa only [Measure.real, Function.comp_def] using
     (ENNReal.tendsto_toReal (measure_ne_top μ Set.univ)).comp hmeasure
 
 /-- A lower-left rectangle has positive mass under a finite open-positive joint law. -/
@@ -2953,7 +2952,7 @@
 -/
 theorem lowerLeftRectangleMass_continuous_of_noAtoms_marginals
     (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
-    [NoAtoms (μ.map Prod.fst)] [NoAtoms (μ.map Prod.snd)] :
+    [NullSingletonClass (μ.map Prod.fst)] [NullSingletonClass (μ.map Prod.snd)] :
     Continuous fun q : ℝ × ℝ => lowerLeftRectangleMass μ q.1 q.2 := by
   refine lowerLeftRectangleMass_continuous_of_boundary_null μ ?_
   intro x y
@@ -3118,7 +3117,7 @@
       (fun q : ℝ =>
         (μ {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2}).toReal)
       Filter.atBot (nhds (μ.real Set.univ))
-  simpa [Measure.real] using
+  simpa only [Measure.real, Function.comp_def] using
     (ENNReal.tendsto_toReal (measure_ne_top μ Set.univ)).comp hmeasure
 
 /--
@@ -3206,7 +3205,7 @@
 -/
 theorem upperOrthantMass_diagonal_continuous_of_noAtoms_marginals
     (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
-    [NoAtoms (μ.map Prod.fst)] [NoAtoms (μ.map Prod.snd)] (offset : ℝ) :
+    [NullSingletonClass (μ.map Prod.fst)] [NullSingletonClass (μ.map Prod.snd)] (offset : ℝ) :
     Continuous fun q : ℝ => upperOrthantMass μ (q - offset) q := by
   refine upperOrthantMass_diagonal_continuous_of_boundary_null μ offset ?_
   intro q
@@ -3309,11 +3308,11 @@
     (hp : MeasurableSet {b | p b}) :
     pmfProb
         (@Measure.toPMF β _ _ _ (μ.map f)
-          (Measure.isProbabilityMeasure_map hf.aemeasurable)) p =
+          ((by infer_instance))) p =
       measureProb μ (fun a => p (f a)) := by
   classical
   haveI : IsProbabilityMeasure (μ.map f) :=
-    Measure.isProbabilityMeasure_map hf.aemeasurable
+    (by infer_instance)
   unfold measureProb
   rw [pmfProb_eq_toOuterMeasure_toReal]
   rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply ((μ.map f).toPMF) hp]
@@ -3357,7 +3356,7 @@
   have hsγ : MeasurableSet {b : γ | s b.1} :=
     hs.preimage measurable_subtype_coe
   let ν : PMF γ := @Measure.toPMF γ _ _ _ (μ.map g)
-    (Measure.isProbabilityMeasure_map hg.aemeasurable)
+    ((by infer_instance))
   have hpmf :
       pmfProb ν (fun b : γ => p b.1) - pmfProb ν (fun b : γ => q b.1) ≤
         pmfProb ν (fun b : γ => r b.1) - pmfProb ν (fun b : γ => s b.1) := by
@@ -3465,7 +3464,7 @@
     simp [U]
   change (μ U).toReal ≤ ∑ i ∈ s, measureProb μ (fun a => p i a)
   rw [hset]
-  simpa [measureProb] using
+  simpa only [measureProb, Measure.real] using
     (measureReal_biUnion_finset_le (μ := μ) (s := s) (f := fun i => {a : α | p i a}))
 
 /-- First-order complement lower bound for finite intersections. -/
@@ -3526,7 +3525,7 @@
       1 - ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) ≤ 1 - μ.real C := by
         nlinarith [hcomp]
       _ = μ.real U := by linarith [hCeq]
-  simpa [measureProb, U] using hprob
+  simpa only [measureProb, U, Measure.real] using hprob
 
 private theorem sum_filter_choose_eq
     {ι α : Type*} (s : Finset ι) (p : ι → α → Prop) (ω : α) (k : ℕ)
```

## GJ19OptimalBinaryRatingSystems/AppendixB.lean

```diff
--- upstream/GJ19OptimalBinaryRatingSystems/AppendixB.lean
+++ lean-4.34.1/GJ19OptimalBinaryRatingSystems/AppendixB.lean
@@ -3490,7 +3490,7 @@
     simpa [sqBound, endpointStart] using hwidthSqRate C hC
   have hsqrt_zero :
       Tendsto (fun M : ℕ => Real.sqrt (sqBound M)) atTop (nhds 0) := by
-    simpa [Real.sqrt_zero] using
+    simpa only [Real.sqrt_zero, Function.comp_def] using
       (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsqBound_zero
   have hendpointStart : 0 < endpointStart := by
     dsimp [endpointStart]
@@ -9291,7 +9291,7 @@
               finiteCutpointVectorEval M v j.1) :=
       (continuous_finiteCutpointVectorEval M (j.1 + 1)).sub
         (continuous_finiteCutpointVectorEval M j.1)
-    simpa [hij] using hi.mul hj
+    convert! hi.mul hj using 1 <;> simp [hij] <;> rfl
   · simpa [hij] using
       (continuous_const :
         Continuous (fun _v : Fin (M + 1) → ℝ => (0 : ℝ)))
@@ -9332,7 +9332,7 @@
               finiteCutpointVectorEval M v j) :=
       (continuous_finiteCutpointVectorEval M (j + 1)).sub
         (continuous_finiteCutpointVectorEval M j)
-    simpa [hij, mul_assoc] using (hleft.mul hi).mul hj
+    convert! (hleft.mul hi).mul hj using 1 <;> simp [hij, mul_assoc] <;> rfl
   · simpa [hij] using
       (continuous_const :
         Continuous (fun _v : Fin (M + 1) → ℝ => (0 : ℝ)))
@@ -9384,7 +9384,7 @@
               finiteCutpointVectorEval M v j) :=
       (continuous_finiteCutpointVectorEval M (j + 1)).sub
         (continuous_finiteCutpointVectorEval M j)
-    simpa [hij, mul_assoc] using (hweight_eval.mul hi).mul hj
+    convert! (hweight_eval.mul hi).mul hj using 1 <;> simp [hij, mul_assoc] <;> rfl
   · simpa [hij] using
       (continuous_const :
         Continuous (fun _v : Fin (M + 1) → ℝ => (0 : ℝ)))
@@ -9716,7 +9716,7 @@
           cutpointRangeFunctional M finiteFunctional
             (EconCSLib.FiniteSum.finiteGapCutpoint gap))
         {gap : Fin M → ℝ | EconCSLib.FiniteProbabilitySimplex gap} := by
-    simpa [cutpointRangeFunctional] using
+    exact
       (hcontinuous.comp (continuous_finiteGapCutpoint_vector (M := M))).continuousOn
   exact
     theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex_of_cutpointRangeFunctional
@@ -10152,22 +10152,22 @@
             EconCSLib.FiniteSum.finiteGapCutpoint gap j.1)
           (component.val.2.val + 1)
     have ha : Tendsto a (𝓝[simplex] gap₀) (𝓝 (a gap₀)) := by
-      simpa [a] using
+      exact
         ((continuous_finiteCutpointVectorEval (m + 2)
           component.val.1.val).comp
           (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousWithinAt
     have hb : Tendsto b (𝓝[simplex] gap₀) (𝓝 (b gap₀)) := by
-      simpa [b] using
+      exact
         ((continuous_finiteCutpointVectorEval (m + 2)
           (component.val.1.val + 1)).comp
           (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousWithinAt
     have hc : Tendsto c (𝓝[simplex] gap₀) (𝓝 (c gap₀)) := by
-      simpa [c] using
+      exact
         ((continuous_finiteCutpointVectorEval (m + 2)
           component.val.2.val).comp
           (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousWithinAt
     have hd : Tendsto d (𝓝[simplex] gap₀) (𝓝 (d gap₀)) := by
-      simpa [d] using
+      exact
         ((continuous_finiteCutpointVectorEval (m + 2)
           (component.val.2.val + 1)).comp
           (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousWithinAt
@@ -10176,16 +10176,16 @@
           Set.Ioc (a gap) (b gap) ×ˢ Set.Ioc (c gap) (d gap) ⊆
             Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
       filter_upwards [self_mem_nhdsWithin] with gap hgap
-      simpa [a, b, c, d] using
+      exact
         finiteCutpointVectorEval_finiteGapCutpoint_Ioc_prod_subset_unit_square
           gap hgap component.val.1.val component.val.2.val
     have hrect₀_subset :
         Set.Ioc (a gap₀) (b gap₀) ×ˢ Set.Ioc (c gap₀) (d gap₀) ⊆
           Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
-      simpa [a, b, c, d] using
+      exact
         finiteCutpointVectorEval_finiteGapCutpoint_Ioc_prod_subset_unit_square
           gap₀ hgap₀ component.val.1.val component.val.2.val
-    simpa [a, b, c, d] using
+    exact
       tendsto_integral_Ioc_prod_of_tendsto_of_integrableOn_Icc
         (l := 𝓝[simplex] gap₀)
         ha hb hc hd hweight_int hrect_subset hrect₀_subset
@@ -10383,7 +10383,7 @@
           cutpointRangeFunctional (m + 2)
             (theorem31SpearmanCellMidpointFiniteObjective m)
             (EconCSLib.FiniteSum.finiteGapCutpoint gap)) := by
-    simpa [cutpointRangeFunctional] using
+    exact
       (continuous_theorem31SpearmanCellMidpointFiniteObjective m).comp
         (continuous_finiteGapCutpoint_vector (M := m + 2))
   refine hpoly.continuousOn.congr ?_
@@ -10890,7 +10890,7 @@
           cutpointRangeFunctional (m + 2) finiteFunctional
             (EconCSLib.FiniteSum.finiteGapCutpoint gap))
         {gap : Fin (m + 2) → ℝ | EconCSLib.FiniteProbabilitySimplex gap} := by
-    simpa [cutpointRangeFunctional] using
+    exact
       (hcontinuous.comp
         (continuous_finiteGapCutpoint_vector (M := m + 2))).continuousOn
   exact
@@ -11859,7 +11859,7 @@
       (equispacedIntervalCutpoint M)
       tstar
       ?hvalue htstar ?hrate
-  · simpa [kendallConstantWeightOrderedPairIntervalObjective] using
+  · exact
       lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
         (M := M) hM
   · intro S t hS ht hvalue_eq
@@ -11868,7 +11868,7 @@
       lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_eq_equispaced_uniform_gap
         (M := M) hM S hS.1 hS.2
         (by
-          simpa [kendallConstantWeightOrderedPairIntervalObjective] using
+          exact
             hvalue_eq)
     exact hrate_uniform S t hS ht huniform
```

## GJ19OptimalBinaryRatingSystems/ExperimentTheorems.lean

```diff
--- upstream/GJ19OptimalBinaryRatingSystems/ExperimentTheorems.lean
+++ lean-4.34.1/GJ19OptimalBinaryRatingSystems/ExperimentTheorems.lean
@@ -127,8 +127,7 @@
           (sourceQuestionPositiveIndicator E i y) N ω)
         atTop (nhds (H y * ψ (quality i) y)) := by
     simpa [sourceExperimentEmpiricalMean, hpositive_mean i y] using hpositive
-  simpa [sourceExperimentEmpiricalQuestionResponse_eq_ratio_means,
-    (hHpos y).ne'] using hpositive'.div hasked' (hHpos y).ne'
+  convert! hpositive'.div hasked' (hHpos y).ne' using 1 <;> simp [sourceExperimentEmpiricalQuestionResponse_eq_ratio_means, (hHpos y).ne'] <;> rfl
 
 /--
 Strong-law step for every coordinate of a fixed finite representative/question
```

## GJ19OptimalBinaryRatingSystems/Assumptions.lean

```diff
--- upstream/GJ19OptimalBinaryRatingSystems/Assumptions.lean
+++ lean-4.34.1/GJ19OptimalBinaryRatingSystems/Assumptions.lean
@@ -1169,7 +1169,7 @@
     change
       Tendsto (EconCSLib.Math.reciprocalThresholdError threshold)
         atTop (nhds 0) at hbase
-    simpa [errSeq, endpointStart] using hbase.comp hidx
+    simpa only [errSeq, endpointStart, Function.comp_def] using hbase.comp hidx
   · intro C hC
     let endpointStart : ℕ := 2 * C - 1
     have hendpointStart_pos : 0 < endpointStart := by
```

## GJ19OptimalBinaryRatingSystems/AuditInterface.lean

```diff
--- upstream/GJ19OptimalBinaryRatingSystems/AuditInterface.lean
+++ lean-4.34.1/GJ19OptimalBinaryRatingSystems/AuditInterface.lean
@@ -9997,7 +9997,7 @@
       (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hlastBracket)
       (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hgrid)
       houter hinner
-  simpa [lemmaC5_uniform_doubled_endpoint_levels] using
+  exact
     binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
       (m := m) (M := M) (L := L)
       hm oldLevels returned heps holdLevels holdEq run
```

## GJ19OptimalBinaryRatingSystems/PaperInterface.lean

```diff
--- upstream/GJ19OptimalBinaryRatingSystems/PaperInterface.lean
+++ lean-4.34.1/GJ19OptimalBinaryRatingSystems/PaperInterface.lean
@@ -372,7 +372,7 @@
       HasExponentialRate
         (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
         (binaryEndpointAwareAdjacentRate levels sampleRate minAdjacent) := by
-    simpa only [theorem31SourceWbar] using
+    exact
       lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_cell_midpoints
         μ hm cut hmono hcut_strict levels sampleRate hlevels hsample_pos
         hsample_mono weight hweight_int hweight_nonneg hweight_cont
```
