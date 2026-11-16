# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

The following exact diffs retain the recorded compatibility choices. Source hash and import-relocation checks do not prove global equivalence of the historical and modern library environments.

## EconCSLib/Foundations/Probability/CTMC.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/CTMC.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/CTMC.lean
@@ -1,3 +1,4 @@
+import Mathlib.Analysis.Calculus.Deriv.Inv
 import Mathlib.Analysis.SpecialFunctions.ExpDeriv
 import Mathlib.Analysis.Convex.SpecificFunctions.Basic
 import Mathlib.Analysis.Calculus.Deriv.Slope
@@ -204,9 +205,8 @@
             Real.exp (-(lambdaIJ + lambdaJI) * t)) * t -
           twoStateCtmcSwitchProb lambdaIJ lambdaJI t) / t ^ 2) t := by
   unfold twoStateCtmcSwitchProbPerTime
-  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
-    (twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI t).div
-      (hasDerivAt_id t) ht
+  convert! (twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI t).div
+      (hasDerivAt_id t) ht using 1 <;> simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
 
 /--
 The switch probability per unit time has negative derivative under positive
```

## EconCSLib/Foundations/Probability/MeasureInequalities.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/MeasureInequalities.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/MeasureInequalities.lean
@@ -309,7 +309,7 @@
         (Ω := fun _ => Bool) (mΩ := fun _ => by infer_instance)
         (P := P) hμ (X := fun i : ι => (fun b : Bool => b))
         (mX := fun _ => measurable_id)
-  simpa [fairBoolProductMeasure, P] using hcoord.comp
+  simpa only [fairBoolProductMeasure, P, Function.comp_def] using hcoord.comp
     (fun _ b => if b = keep then (1 : ℝ) else 0)
     (fun _ => measurable_of_finite _)
 
@@ -796,7 +796,7 @@
 -/
 theorem lowerLeftRectangleMass_continuous_of_noAtoms_marginals
     (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
-    [NoAtoms (μ.map Prod.fst)] [NoAtoms (μ.map Prod.snd)] :
+    [NullSingletonClass (μ.map Prod.fst)] [NullSingletonClass (μ.map Prod.snd)] :
     Continuous fun q : ℝ × ℝ => lowerLeftRectangleMass μ q.1 q.2 := by
   refine lowerLeftRectangleMass_continuous_of_boundary_null μ ?_
   intro x y
@@ -961,7 +961,7 @@
       (fun q : ℝ =>
         (μ {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2}).toReal)
       Filter.atBot (nhds (μ.real Set.univ))
-  simpa [Measure.real] using
+  simpa only [Measure.real, Function.comp_def] using
     (ENNReal.tendsto_toReal (measure_ne_top μ Set.univ)).comp hmeasure
 
 /--
@@ -1049,7 +1049,7 @@
 -/
 theorem upperOrthantMass_diagonal_continuous_of_noAtoms_marginals
     (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
-    [NoAtoms (μ.map Prod.fst)] [NoAtoms (μ.map Prod.snd)] (offset : ℝ) :
+    [NullSingletonClass (μ.map Prod.fst)] [NullSingletonClass (μ.map Prod.snd)] (offset : ℝ) :
     Continuous fun q : ℝ => upperOrthantMass μ (q - offset) q := by
   refine upperOrthantMass_diagonal_continuous_of_boundary_null μ offset ?_
   intro q
@@ -1152,11 +1152,11 @@
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
@@ -1200,7 +1200,7 @@
   have hsγ : MeasurableSet {b : γ | s b.1} :=
     hs.preimage measurable_subtype_coe
   let ν : PMF γ := @Measure.toPMF γ _ _ _ (μ.map g)
-    (Measure.isProbabilityMeasure_map hg.aemeasurable)
+    ((by infer_instance))
   have hpmf :
       pmfProb ν (fun b : γ => p b.1) - pmfProb ν (fun b : γ => q b.1) ≤
         pmfProb ν (fun b : γ => r b.1) - pmfProb ν (fun b : γ => s b.1) := by
@@ -1308,7 +1308,7 @@
     simp [U]
   change (μ U).toReal ≤ ∑ i ∈ s, measureProb μ (fun a => p i a)
   rw [hset]
-  simpa [measureProb] using
+  simpa only [measureProb, Measure.real] using
     (measureReal_biUnion_finset_le (μ := μ) (s := s) (f := fun i => {a : α | p i a}))
 
 /-- First-order complement lower bound for finite intersections. -/
@@ -1369,7 +1369,7 @@
       1 - ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) ≤ 1 - μ.real C := by
         nlinarith [hcomp]
       _ = μ.real U := by linarith [hCeq]
-  simpa [measureProb, U] using hprob
+  simpa only [measureProb, U, Measure.real] using hprob
 
 private theorem sum_filter_choose_eq
     {ι α : Type*} (s : Finset ι) (p : ι → α → Prop) (ω : α) (k : ℕ)
```

## GN21DriverSurgePricing/MainTheorems.lean

```diff
--- upstream/GN21DriverSurgePricing/MainTheorems.lean
+++ lean-4.34.1/GN21DriverSurgePricing/MainTheorems.lean
@@ -1485,7 +1485,7 @@
   have hmeasure_pos : 0 < μ σ := by
     by_contra hnot_pos
     have hmeasure_zero : μ σ = 0 := by
-      exact le_antisymm (le_of_not_gt hnot_pos) (zero_le _)
+      exact le_antisymm (le_of_not_gt hnot_pos) (zero_le)
     have hrestrict_zero : μ.restrict σ = 0 :=
       Measure.restrict_eq_zero.2 hmeasure_zero
     unfold singleStateTripTime at htime_pos
@@ -1539,7 +1539,7 @@
   have hmeasure_pos : 0 < μ σ := by
     by_contra hnot_pos
     have hmeasure_zero : μ σ = 0 := by
-      exact le_antisymm (le_of_not_gt hnot_pos) (zero_le _)
+      exact le_antisymm (le_of_not_gt hnot_pos) (zero_le)
     have hrestrict_zero : μ.restrict σ = 0 :=
       Measure.restrict_eq_zero.2 hmeasure_zero
     unfold singleStateTripTime at htime_pos
@@ -3766,7 +3766,7 @@
             (1 + arrivalRate * singleStateTripTime μ σ)))
         hw_integrable_added hadded_measurable hpointwise
     rw [integral_const_mul] at hmono
-    simpa [mul_assoc] using hmono
+    simpa [mul_assoc, singleStateTripTime, singleStateTripPayment] using hmono
   change
     renewalRewardRate arrivalRate
         (singleStateTripPayment μ w σ) (singleStateTripTime μ σ) ≤
@@ -3844,7 +3844,7 @@
             (1 + arrivalRate * singleStateTripTime μ σ)))
         hremoved_measurable hpointwise
     rw [integral_const_mul] at hmono
-    simpa [mul_assoc] using hmono
+    simpa [mul_assoc, singleStateTripTime, singleStateTripPayment] using hmono
   change
     renewalRewardRate arrivalRate
         (singleStateTripPayment μ w σ) (singleStateTripTime μ σ) ≤
@@ -8572,6 +8572,8 @@
 def dynamicMeasurableIncentiveCompatible (R : DynamicReward) : Prop :=
   dynamicMeasurableOptimal R acceptAllDynamicPolicy
 
+attribute [local simp] dynamicMeasurableIncentiveCompatible
+
 /--
 Dynamic optimality restricted to feasible measurable policies whose accepted
 trip mass is positive in both states.
@@ -10054,6 +10056,8 @@
 def ctmcStructuredSurgePrice
     (m z lambdaIJ lambdaJI : ℝ) : PricingFunction :=
   structuredSurgePrice m z (gn21SwitchProb lambdaIJ lambdaJI)
+
+attribute [local simp] ctmcStructuredSurgePrice
 
 /--
 Structured CTMC prices are integrable on a policy set whenever trip time and
@@ -11127,9 +11131,9 @@
     have hq :
         HasDerivAt (fun s => gn21SwitchProb lambdaIJ lambdaJI s)
           (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * τ)) τ := by
-      convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI τ using 1
-      field_simp [ne_of_gt hsum]
-    simpa [mul_comm] using ((hasDerivAt_id τ).const_mul lambdaIJ).sub hq
+      unfold gn21SwitchProb
+      convert! twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI τ using 1 <;> field_simp [ne_of_gt hsum]
+    convert! ((hasDerivAt_id τ).const_mul lambdaIJ).sub hq using 1 <;> simp [mul_comm]
   rw [hderiv.deriv]
   have harg : -(lambdaIJ + lambdaJI) * τ ≤ 0 := by nlinarith
   have hexp_le_one : Real.exp (-(lambdaIJ + lambdaJI) * τ) ≤ 1 := by
@@ -11155,9 +11159,9 @@
     have hq :
         HasDerivAt (fun s => gn21SwitchProb lambdaIJ lambdaJI s)
           (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * τ)) τ := by
-      convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI τ using 1
-      field_simp [ne_of_gt hsum]
-    simpa [mul_comm] using ((hasDerivAt_id τ).const_mul lambdaIJ).sub hq
+      unfold gn21SwitchProb
+      convert! twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI τ using 1 <;> field_simp [ne_of_gt hsum]
+    convert! ((hasDerivAt_id τ).const_mul lambdaIJ).sub hq using 1 <;> simp [mul_comm]
   rw [hderiv.deriv]
   have harg : -(lambdaIJ + lambdaJI) * τ < 0 := by nlinarith
   have hexp_lt_one : Real.exp (-(lambdaIJ + lambdaJI) * τ) < 1 := by
@@ -11178,8 +11182,8 @@
     have hq :
         HasDerivAt (fun s => gn21SwitchProb lambdaIJ lambdaJI s)
           (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * τ)) τ := by
-      convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI τ using 1
-      field_simp [ne_of_gt hsum]
+      unfold gn21SwitchProb
+      convert! twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI τ using 1 <;> field_simp [ne_of_gt hsum]
     exact (((hasDerivAt_id τ).const_mul lambdaIJ).sub hq).continuousAt.continuousWithinAt
   · intro τ hτ
     have hτ_pos : 0 < τ := by
@@ -13339,7 +13343,8 @@
   have hden_path :
       QiPath u * Tj + Qj * TiPath u ≠ 0 := by
     simpa [hQi_val, hTi_val] using hden
-  convert hnum.div hden_deriv hden_path using 1
+  unfold gn21AggregateDynamicReward
+  convert! hnum.div hden_deriv hden_path using 1
   rw [hQi_val, hWi_val, hTi_val]
   unfold gn21DerivativeSignKernel
   field_simp [hden]
@@ -13599,8 +13604,8 @@
   have hq :
       HasDerivAt (fun x => gn21SwitchProb lambdaIJ lambdaJI x)
         (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * u)) u := by
-    convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI u using 1
-    field_simp [hsum]
+    unfold gn21SwitchProb
+    convert! twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI u using 1 <;> field_simp [hsum]
   have hnum :
       HasDerivAt
         (fun x => c1 - c2 * gn21SwitchProb lambdaIJ lambdaJI x)
@@ -13609,7 +13614,8 @@
   have hdiv :=
     hnum.div (hasDerivAt_id u) hu
   have hresp := hdiv.add_const c3
-  convert hresp using 1
+  unfold gn21Lemma7CanonicalResponse
+  convert! hresp using 1
   unfold gn21Lemma7CanonicalDerivativeNumerator
   simp [id]
   ring_nf
@@ -13628,8 +13634,8 @@
   have hq :
       HasDerivAt (fun x => gn21SwitchProb lambdaIJ lambdaJI x)
         (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * u)) u := by
-    convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI u using 1
-    field_simp [hsum]
+    unfold gn21SwitchProb
+    convert! twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI u using 1 <;> field_simp [hsum]
   have hlin :
       HasDerivAt (fun x : ℝ => -(lambdaIJ + lambdaJI) * x)
         (-(lambdaIJ + lambdaJI)) u := by
@@ -13655,11 +13661,12 @@
           u * (lambdaIJ *
             (Real.exp (-(lambdaIJ + lambdaJI) * u) *
               (-(lambdaIJ + lambdaJI))))) u := by
-    simpa using (hasDerivAt_id u).mul hscaled_exp
+    convert! (hasDerivAt_id u).mul hscaled_exp using 1 <;> simp
   have hdiff :=
     hq.sub hproduct
   have hnum := (hdiff.const_mul c2).sub_const c1
-  convert hnum using 1
+  unfold gn21Lemma7CanonicalDerivativeNumerator
+  convert! hnum using 1
   ring
 
 /-- Lemma 7 derivative numerator is strictly increasing at positive trip lengths. -/
@@ -14026,6 +14033,8 @@
     exact sameStrictSign_of_pos_mul_left D.scale
       (gn21DerivativeSignKernel D.q D.u D.wi D.Qi D.Qj D.Ti D.Tj D.Wi D.Wj)
       D.scale_pos
+
+attribute [local simp] lemma6DerivativeFormulaCertificate_of_endpoint_data
 
 /-- Lemma 6 endpoint data include the promised analytic derivative statement. -/
 theorem paper_lemma6_endpoint_hasDerivAt_of_data
@@ -14663,6 +14672,8 @@
   derivative_eq_scaled_kernel := by
     field_simp [hden]
 
+attribute [local simp] lemma6EndpointDerivativeData_of_aggregate_paths
+
 /--
 Aggregate-path form of Lemma 6: once the endpoint derivatives of `Q_i`,
 `W_i`, and `T_i` are known, the derivative of the aggregate reward quotient
@@ -14812,6 +14823,8 @@
         ht_int ht_meas ht_cont using 1
       ring)
     rfl rfl rfl hden
+
+attribute [local simp] lemma6EndpointDerivativeData_of_interval_density_paths
 
 /--
 Interval-density form of Lemma 6: under the source density assumptions for a
@@ -17151,7 +17164,7 @@
 to the merged open interval in the paper's a.e. policy convention.
 -/
 theorem policyAlmostEverywhereEq_ioo_union_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {a b c : TripLength} (hab : a ≤ b) (hbc : b ≤ c) :
     policyAlmostEverywhereEq μ
       (Set.Ioo a b ∪ Set.Ioo b c) (Set.Ioo a c) := by
@@ -17191,7 +17204,7 @@
 to the merged right ray.
 -/
 theorem policyAlmostEverywhereEq_ioo_union_Ioi_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {a b : TripLength} (hab : a ≤ b) :
     policyAlmostEverywhereEq μ
       (Set.Ioo a b ∪ Set.Ioi b) (Set.Ioi a) := by
@@ -17206,7 +17219,7 @@
 Lemma 5 boundary-tail reduction.
 -/
 theorem policyAlmostEverywhereEq_bounded_union_positiveRightRay_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {a b : TripLength} (ha : 0 ≤ a) (hab : a ≤ b) :
     policyAlmostEverywhereEq μ
       (Set.Ioo a b ∪
@@ -17268,7 +17281,7 @@
 a.e. equal to the merged positive left ray.
 -/
 theorem policyAlmostEverywhereEq_positiveLeftRay_union_bounded_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {a b : TripLength} (ha : 0 ≤ a) (hab : a ≤ b) :
     policyAlmostEverywhereEq μ
       ((GN21GeneralizedIntervalComponent.positiveLeftRay a).policy ∪
@@ -17312,7 +17325,7 @@
 the full positive trip domain.
 -/
 theorem policyAlmostEverywhereEq_positiveLeftRightRay_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (a : TripLength) :
     policyAlmostEverywhereEq μ
       ((GN21GeneralizedIntervalComponent.positiveLeftRay a).policy ∪
@@ -17330,7 +17343,7 @@
 by the merged interval, modulo the paper's a.e. endpoint convention.
 -/
 theorem lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -17378,7 +17391,7 @@
 Strict version of `lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path`.
 -/
 theorem lemma5_upper_endpoint_merge_reward_gt_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -17428,7 +17441,7 @@
 while the upper endpoint of one interval moves to the next lower endpoint.
 -/
 theorem lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17485,7 +17498,7 @@
 `lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path_with_context`.
 -/
 theorem lemma5_upper_endpoint_merge_reward_gt_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17546,7 +17559,7 @@
 paper's subcase iteration.
 -/
 theorem lemma5_upper_endpoint_merge_or_first_zero_reward_gt_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17622,7 +17635,7 @@
 stops at the first derivative sign change.
 -/
 theorem lemma5_upper_endpoint_merge_or_first_zero_exists_strict_improvement_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17671,7 +17684,7 @@
 with all other intervals held fixed.
 -/
 theorem lemma5_lower_endpoint_merge_reward_ge_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17727,7 +17740,7 @@
 Strict context-aware lower-endpoint merge step.
 -/
 theorem lemma5_lower_endpoint_merge_reward_gt_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17786,7 +17799,7 @@
 the last zero of the derivative proxy.  Both branches strictly improve reward.
 -/
 theorem lemma5_lower_endpoint_merge_or_last_zero_reward_gt_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17861,7 +17874,7 @@
 strict-local optimality arguments.
 -/
 theorem lemma5_lower_endpoint_merge_or_last_zero_exists_strict_improvement_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -18923,7 +18936,7 @@
 strictly smaller endpoint complexity.
 -/
 theorem lemma5_twoBounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -18974,7 +18987,7 @@
 `lemma5_twoBounded_upper_merge_step_of_endpoint_path`.
 -/
 theorem lemma5_twoBounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19027,7 +19040,7 @@
 lowering component count by one.
 -/
 theorem lemma5_withTwoBounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -19082,7 +19095,7 @@
 `lemma5_withTwoBounded_upper_merge_step_of_endpoint_path`.
 -/
 theorem lemma5_withTwoBounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -19138,7 +19151,7 @@
 components are replaced by one merged bounded interval.
 -/
 theorem lemma5_withTwoBounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -19193,7 +19206,7 @@
 `lemma5_withTwoBounded_lower_merge_step_of_endpoint_path`.
 -/
 theorem lemma5_withTwoBounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -19249,7 +19262,7 @@
 arbitrary ordered tail held fixed as context.
 -/
 theorem lemma5_list_bounded_bounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19312,7 +19325,7 @@
 Strict ordered-list upper-endpoint merge for the first two bounded components.
 -/
 theorem lemma5_list_bounded_bounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19375,7 +19388,7 @@
 Ordered-list lower-endpoint merge for the first two bounded components.
 -/
 theorem lemma5_list_bounded_bounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19438,7 +19451,7 @@
 Strict ordered-list lower-endpoint merge for the first two bounded components.
 -/
 theorem lemma5_list_bounded_bounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19678,7 +19691,7 @@
 right ray becomes one positive right ray.
 -/
 theorem lemma5_list_bounded_rightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19766,7 +19779,7 @@
 Strict ordered-list right-tail merge.
 -/
 theorem lemma5_list_bounded_rightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19857,7 +19870,7 @@
 right-tail version of the source quasi-convex Subcase 1C move.
 -/
 theorem lemma5_list_bounded_rightRay_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19943,7 +19956,7 @@
 Strict ordered-list right-tail lower-endpoint merge.
 -/
 theorem lemma5_list_bounded_rightRay_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20032,7 +20045,7 @@
 source quasi-convex Subcase 1B move.
 -/
 theorem lemma5_list_leftRay_bounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20120,7 +20133,7 @@
 Strict ordered-list left-boundary upper-endpoint merge.
 -/
 theorem lemma5_list_leftRay_bounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20209,7 +20222,7 @@
 component becomes one larger positive left ray.
 -/
 theorem lemma5_list_leftRay_bounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20297,7 +20310,7 @@
 Strict ordered-list left-tail merge.
 -/
 theorem lemma5_list_leftRay_bounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20387,7 +20400,7 @@
 endpoint to the right ray.
 -/
 theorem lemma5_list_leftRightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20471,7 +20484,7 @@
 Strict ordered-list accept-all merge by moving the left ray's upper endpoint.
 -/
 theorem lemma5_list_leftRightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20797,7 +20810,7 @@
 peeled off the first component.
 -/
 theorem lemma5_list_second_bounded_bounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20870,7 +20883,7 @@
 components.
 -/
 theorem lemma5_list_second_bounded_bounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20943,7 +20956,7 @@
 preserving one leading component and the tail.
 -/
 theorem lemma5_list_second_bounded_bounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21016,7 +21029,7 @@
 components.
 -/
 theorem lemma5_list_second_bounded_bounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21090,7 +21103,7 @@
 one positive right ray.
 -/
 theorem lemma5_list_second_bounded_rightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21177,7 +21190,7 @@
 Strict ordered-list right-tail merge for the second component.
 -/
 theorem lemma5_list_second_bounded_rightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21266,7 +21279,7 @@
 ray merge by moving the ray lower endpoint left.
 -/
 theorem lemma5_list_second_bounded_rightRay_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21351,7 +21364,7 @@
 Strict ordered-list right-tail lower-endpoint merge for the second component.
 -/
 theorem lemma5_list_second_bounded_rightRay_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21439,7 +21452,7 @@
 tail form.
 -/
 theorem lemma5_withBoundedRightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21523,7 +21536,7 @@
 Strict contextual right-tail merge move.
 -/
 theorem lemma5_withBoundedRightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21609,7 +21622,7 @@
 bounded interval's upper endpoint.
 -/
 theorem lemma5_withBoundedRightRay_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21691,7 +21704,7 @@
 Strict contextual right-tail lower-endpoint merge move.
 -/
 theorem lemma5_withBoundedRightRay_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21774,7 +21787,7 @@
 bounded interval merge into one larger positive left ray.
 -/
 theorem lemma5_withLeftRayBounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21862,7 +21875,7 @@
 to the bounded interval's lower endpoint.
 -/
 theorem lemma5_withLeftRayBounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21948,7 +21961,7 @@
 Strict contextual left-boundary upper-endpoint merge move.
 -/
 theorem lemma5_withLeftRayBounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22034,7 +22047,7 @@
 Strict contextual left-boundary merge move.
 -/
 theorem lemma5_withLeftRayBounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22122,7 +22135,7 @@
 positive domain.
 -/
 theorem lemma5_withLeftRightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22205,7 +22218,7 @@
 endpoint right.
 -/
 theorem lemma5_withLeftRightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22288,7 +22301,7 @@
 left to the preceding left ray.
 -/
 theorem lemma5_withLeftRightRay_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22371,7 +22384,7 @@
 endpoint left.
 -/
 theorem lemma5_withLeftRightRay_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22929,7 +22942,7 @@
 under a nonatomic trip-length measure it is accept-all up to a null set.
 -/
 theorem acceptAllAlmostEverywhere_of_rejectsMiddleTrips_self_of_subsetAcceptAll
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {σ : TripPolicy} {t : ℝ}
     (hshape : rejectsMiddleTrips t t σ)
     (hsub : σ ⊆ acceptAllPolicy) :
@@ -22950,7 +22963,7 @@
 single boundary trip length.
 -/
 theorem singleStateRenewalReward_rejectMiddleTripsPolicy_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ) (w : PricingFunction) (t : ℝ)
     (hw_integrable_acceptAll : IntegrableOn w acceptAllPolicy μ)
     (htime_integrable_acceptAll :
@@ -22986,7 +22999,7 @@
 coincident-cutoff middle-rejection shape.
 -/
 theorem singleStateRenewalReward_rejectsMiddleTrips_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ) (w : PricingFunction) (σ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σ)
     (hsub : σ ⊆ acceptAllPolicy)
@@ -23006,7 +23019,7 @@
 middle-rejection policy under a nonatomic trip-length measure.
 -/
 theorem gn21ExitWeightIntegral_rejectMiddleTripsPolicy_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate switchIJ switchJI t : ℝ)
     (hq_integrable_acceptAll :
       IntegrableOn
@@ -23045,7 +23058,7 @@
 middle-rejection policy under a nonatomic trip-length measure.
 -/
 theorem gn21ScaledStateTime_rejectMiddleTripsPolicy_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate t : ℝ)
     (htime_integrable_acceptAll :
       IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ) :
@@ -23079,7 +23092,7 @@
 middle-rejection policy under a nonatomic trip-length measure.
 -/
 theorem gn21ScaledStateEarning_rejectMiddleTripsPolicy_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ) (w : PricingFunction) (t : ℝ)
     (hw_integrable_acceptAll : IntegrableOn w acceptAllPolicy μ) :
     gn21ScaledStateEarning μ arrivalRate w (rejectMiddleTripsPolicy t t) =
@@ -23112,7 +23125,7 @@
 coincident-cutoff middle-rejection policy.
 -/
 theorem gn21ExitWeightIntegral_rejectsMiddleTrips_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate switchIJ switchJI : ℝ)
     (σ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σ)
@@ -23135,7 +23148,7 @@
 coincident-cutoff middle-rejection policy.
 -/
 theorem gn21ScaledStateTime_rejectsMiddleTrips_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ)
     (σ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σ)
@@ -23155,7 +23168,7 @@
 coincident-cutoff middle-rejection policy.
 -/
 theorem gn21ScaledStateEarning_rejectsMiddleTrips_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ) (w : PricingFunction)
     (σ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σ)
@@ -24479,7 +24492,7 @@
 theorem GN21WithDensityAcceptAllSupport.noAtoms
     {μ : Measure TripLength}
     (D : GN21WithDensityAcceptAllSupport μ) :
-    NoAtoms μ := by
+    NullSingletonClass μ := by
   rw [D.hμ]
   infer_instance
 
@@ -24674,7 +24687,7 @@
     (hshape : rejectsMiddleTrips t t σ)
     (hsub : σ ⊆ acceptAllPolicy) :
     acceptAllAlmostEverywhere μ σ := by
-  haveI : NoAtoms μ := D.noAtoms
+  haveI : NullSingletonClass μ := D.noAtoms
   exact
     acceptAllAlmostEverywhere_of_rejectsMiddleTrips_self_of_subsetAcceptAll
       μ hshape hsub
@@ -25497,7 +25510,7 @@
 -/
 theorem
     lemma5_strictlyIncreasing_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (response : TripLength → ℝ)
@@ -25721,7 +25734,7 @@
 -/
 theorem
     lemma5_strictlyDecreasing_gap_exists_strict_improvement_of_stopped_endpoint_paths_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (response : TripLength → ℝ)
@@ -25976,7 +25989,7 @@
 -/
 theorem
     lemma5_strictQuasiConvex_three_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (response : TripLength → ℝ)
@@ -26374,7 +26387,7 @@
 -/
 theorem
     lemma5_strictQuasiConcave_two_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (response : TripLength → ℝ)
@@ -28751,7 +28764,7 @@
 theorem Lemma5PositiveResponseShapeData.positive_zero_set_null
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ] :
+    (μ : Measure TripLength) [NullSingletonClass μ] :
     μ ({τ : TripLength | 0 < τ ∧ response τ = 0}) = 0 := by
   cases D with
   | positive hpositive =>
@@ -28864,7 +28877,7 @@
   policy_form :
     lemma5PolicyForm shape (lemma5PositiveResponsePolicy response)
   positive_zero_set_null :
-    ∀ (μ : Measure TripLength) [NoAtoms μ],
+    ∀ (μ : Measure TripLength) [NullSingletonClass μ],
       μ ({τ : TripLength | 0 < τ ∧ response τ = 0}) = 0
 
 /-- The existing analytic response-shape package implies the smaller policy-form package. -/
@@ -29067,7 +29080,7 @@
 theorem Lemma5PositiveResponsePolicyFormData.policyAlmostEverywhereEq_positiveResponse_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponsePolicyFormData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29116,7 +29129,7 @@
 theorem Lemma5PositiveResponsePolicyFormData.policyFormAlmostEverywhere_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponsePolicyFormData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29140,7 +29153,7 @@
 def Lemma5PositiveResponsePolicyFormData.feasiblePolicyFormAlmostEverywhere_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponsePolicyFormData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29170,7 +29183,7 @@
 def Lemma5PositiveResponsePolicyFormData.feasiblePolicyFormAlmostEverywhere_of_feasible_optimal
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponsePolicyFormData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29197,7 +29210,7 @@
 policy-form data instead of stronger analytic response-shape data.
 -/
 def paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (response : TripLength → ℝ) {shape : Lemma5DerivativeShape}
     (σ : TripPolicy)
     (D : Lemma5PositiveResponsePolicyFormData response shape)
@@ -29224,7 +29237,7 @@
 theorem Lemma5PositiveResponseShapeData.policyAlmostEverywhereEq_positiveResponse_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29273,7 +29286,7 @@
 theorem Lemma5PositiveResponseShapeData.policyFormAlmostEverywhere_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29300,7 +29313,7 @@
 def Lemma5PositiveResponseShapeData.feasiblePolicyFormAlmostEverywhere_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29329,7 +29342,7 @@
 theorem Lemma5PositiveResponseShapeData.policyFormAlmostEverywhere_of_feasible_optimal
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29359,7 +29372,7 @@
 def Lemma5PositiveResponseShapeData.feasiblePolicyFormAlmostEverywhere_of_feasible_optimal
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29388,7 +29401,7 @@
 the canonical Lemma 5 policy form, modulo null boundary sets.
 -/
 theorem paper_lemma5_fixed_response_policy_form_ae_of_response_shape
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (response : TripLength → ℝ) {shape : Lemma5DerivativeShape}
     (σ : TripPolicy)
     (D : Lemma5PositiveResponseShapeData response shape)
@@ -29413,7 +29426,7 @@
 kept explicit for downstream Theorem 4 endpoint moves.
 -/
 def paper_lemma5_fixed_response_feasible_policy_form_ae_of_response_shape
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (response : TripLength → ℝ) {shape : Lemma5DerivativeShape}
     (σ : TripPolicy)
     (D : Lemma5PositiveResponseShapeData response shape)
@@ -29442,7 +29455,7 @@
 theorem Lemma5PositiveResponseShapeData.marginalSetReward_lt_positiveResponsePolicy_of_not_policyFormAE
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29472,7 +29485,7 @@
 sets.
 -/
 theorem paper_lemma5_marginal_optimizer_replacement_ae_of_response_shape
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (response : TripLength → ℝ)
     (σ0 : TripPolicy) (shape : Lemma5DerivativeShape)
     (hresponse_measurable : Measurable response)
@@ -31118,6 +31131,8 @@
         lemma5MarginalSetReward_lt_positiveResponsePolicy_of_accepts_negative_mass
           μ response σ0 hresponse_measurable hresponse_integrable_acceptAll
           hσ0_measurable hσ0_subset hnegative
+
+attribute [local simp] lemma5MarginalOptimizerReplacementCertificate_positiveResponse
 
 /--
 Paper-facing fixed-response Lemma 5 endpoint: the positive-response policy is
@@ -35566,6 +35581,8 @@
             (dynamicStateReward R ρ 1) (ρ 1) sshape hsreplacement
             (dynamicStateReward_optimal_of_dynamicOptimal R hρ 1)⟩⟩
 
+attribute [local simp] theorem4ShapeDerivationCertificate_of_shape_replacement
+
 /--
 Theorem 4 all-optimal replacement certificate: the analytic Lemma 5 step is
 available for every dynamic optimum, but the caller does not need to choose a
@@ -36474,6 +36491,8 @@
           C.nonsurge_positive_form ρ hρ⟩,
         ⟨.positive, theorem4SurgeAllowedLemma5Shape_positive,
           C.surge_positive_form ρ hρ⟩⟩
+
+attribute [local simp] theorem4ShapeDerivationCertificate_of_accept_all_derivation
 
 /--
 When Lemma 9/10 force positive Lemma 5 forms for every optimal policy,
@@ -38792,7 +38811,7 @@
 accept-all in that state.
 -/
 theorem gn21MeasuredAggregateRewardPrimitives_rejectsMiddle_self_eq_acceptAll_left_of_noAtoms
-    (μI μJ : Measure TripLength) [NoAtoms μI]
+    (μI μJ : Measure TripLength) [NullSingletonClass μI]
     (arrivalI arrivalJ switchIJ switchJI : ℝ)
     (wI wJ : PricingFunction) (σI σJ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σI)
@@ -38823,7 +38842,7 @@
 accept-all in that state.
 -/
 theorem gn21MeasuredAggregateRewardPrimitives_rejectsMiddle_self_eq_acceptAll_right_of_noAtoms
-    (μI μJ : Measure TripLength) [NoAtoms μJ]
+    (μI μJ : Measure TripLength) [NullSingletonClass μJ]
     (arrivalI arrivalJ switchIJ switchJI : ℝ)
     (wI wJ : PricingFunction) (σI σJ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σJ)
@@ -50174,7 +50193,7 @@
 -/
 def Theorem4AllMeasurableFixedResponseShapeData.to_feasible_ae_policy_forms
     {μ : Fin 2 → Measure TripLength} {R : DynamicReward}
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (C : Theorem4AllMeasurableFixedResponseShapeData μ R) :
     Theorem4AllMeasurableFeasibleAEPolicyFormData μ R where
   exists_optimal := C.exists_optimal
@@ -50216,7 +50235,7 @@
 Lemma 5 representative.
 -/
 def Lemma5FixedResponsePolicyFormFeasibleOptimalData.to_feasiblePolicyFormAlmostEverywhere
-    {μ : Measure TripLength} [NoAtoms μ]
+    {μ : Measure TripLength} [NullSingletonClass μ]
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     {σ : TripPolicy}
     (D : Lemma5FixedResponsePolicyFormFeasibleOptimalData μ response shape σ)
@@ -50525,7 +50544,7 @@
 -/
 def Theorem4AllMeasurableFixedResponsePolicyFormData.to_feasible_ae_policy_forms
     {μ : Fin 2 → Measure TripLength} {R : DynamicReward}
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (C : Theorem4AllMeasurableFixedResponsePolicyFormData μ R) :
     Theorem4AllMeasurableFeasibleAEPolicyFormData μ R where
   exists_optimal := C.exists_optimal
@@ -51219,7 +51238,7 @@
 -/
 def theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_fixed_response_policy_forms_and_representative_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -51295,7 +51314,7 @@
 -/
 def theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementExistenceCertificate_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -51369,7 +51388,7 @@
 -/
 def theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -51448,7 +51467,7 @@
 -/
 theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -51531,7 +51550,7 @@
 -/
 theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -88102,7 +88121,7 @@
 -/
 def theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_fixed_response_policy_forms
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (C :
@@ -88176,7 +88195,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -88342,7 +88361,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.to_source_data
     {μ : Fin 2 → Measure TripLength}
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     {arrival m z : Fin 2 → ℝ}
     {switch12 switch21 : ℝ}
     (D :
@@ -89556,7 +89575,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_by_policy_form_middle_cutoff_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -90032,7 +90051,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_cross_by_policy_form_middle_cutoff_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -90340,7 +90359,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_eq_middle_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -90677,7 +90696,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_eq_middle_cutoff_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -91050,7 +91069,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceData.of_fixed_state_eq_middle_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -91313,7 +91332,7 @@
 -/
 def theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_fixed_response_policy_form_rejected_mass
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (C :
@@ -91387,7 +91406,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_rejected_mass_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91412,7 +91431,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_rejected_mass_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91431,7 +91450,7 @@
 -/
 def theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_fixed_response_policy_form_rejected_mass_existence
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (C :
@@ -91505,7 +91524,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_rejected_mass_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91530,7 +91549,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_rejected_mass_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91548,7 +91567,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91595,7 +91614,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91613,7 +91632,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91661,7 +91680,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91679,7 +91698,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91717,7 +91736,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -91995,7 +92014,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -92185,7 +92204,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_eq_middle_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -92271,7 +92290,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -92437,7 +92456,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -92627,7 +92646,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_eq_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -92713,7 +92732,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -93904,7 +93923,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -93942,7 +93961,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94006,7 +94025,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94044,7 +94063,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94108,7 +94127,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94146,7 +94165,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94213,7 +94232,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cutoff_branch_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94251,7 +94270,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_surge_cutoff_branch_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94318,7 +94337,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94356,7 +94375,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94461,7 +94480,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_branch_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94478,7 +94497,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_exact_one_threshold_branch_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94495,7 +94514,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_branch_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94581,7 +94600,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94620,7 +94639,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94684,7 +94703,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94722,7 +94741,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94786,7 +94805,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94824,7 +94843,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94923,7 +94942,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_bracket_branch_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94940,7 +94959,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_exact_one_threshold_bracket_branch_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -94958,7 +94977,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_bracket_branch_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -96318,7 +96337,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_reroute_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
```
