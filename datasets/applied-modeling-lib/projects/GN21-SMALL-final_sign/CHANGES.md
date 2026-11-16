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
 
@@ -742,7 +742,7 @@
       (fun q : ℝ =>
         (μ {p : ℝ × ℝ | p.1 ≤ a q ∧ b q ≤ p.2}).toReal)
       Filter.atBot (nhds (μ.real Set.univ))
-  simpa [Measure.real] using
+  simpa only [Measure.real, Function.comp_def] using
     (ENNReal.tendsto_toReal (measure_ne_top μ Set.univ)).comp hmeasure
 
 /-- A lower-left rectangle has positive mass under a finite open-positive joint law. -/
@@ -934,7 +934,7 @@
 -/
 theorem lowerLeftRectangleMass_continuous_of_noAtoms_marginals
     (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
-    [NoAtoms (μ.map Prod.fst)] [NoAtoms (μ.map Prod.snd)] :
+    [NullSingletonClass (μ.map Prod.fst)] [NullSingletonClass (μ.map Prod.snd)] :
     Continuous fun q : ℝ × ℝ => lowerLeftRectangleMass μ q.1 q.2 := by
   refine lowerLeftRectangleMass_continuous_of_boundary_null μ ?_
   intro x y
@@ -1099,7 +1099,7 @@
       (fun q : ℝ =>
         (μ {p : ℝ × ℝ | q - offset ≤ p.1 ∧ q ≤ p.2}).toReal)
       Filter.atBot (nhds (μ.real Set.univ))
-  simpa [Measure.real] using
+  simpa only [Measure.real, Function.comp_def] using
     (ENNReal.tendsto_toReal (measure_ne_top μ Set.univ)).comp hmeasure
 
 /--
@@ -1187,7 +1187,7 @@
 -/
 theorem upperOrthantMass_diagonal_continuous_of_noAtoms_marginals
     (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
-    [NoAtoms (μ.map Prod.fst)] [NoAtoms (μ.map Prod.snd)] (offset : ℝ) :
+    [NullSingletonClass (μ.map Prod.fst)] [NullSingletonClass (μ.map Prod.snd)] (offset : ℝ) :
     Continuous fun q : ℝ => upperOrthantMass μ (q - offset) q := by
   refine upperOrthantMass_diagonal_continuous_of_boundary_null μ offset ?_
   intro q
@@ -1290,11 +1290,11 @@
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
@@ -1338,7 +1338,7 @@
   have hsγ : MeasurableSet {b : γ | s b.1} :=
     hs.preimage measurable_subtype_coe
   let ν : PMF γ := @Measure.toPMF γ _ _ _ (μ.map g)
-    (Measure.isProbabilityMeasure_map hg.aemeasurable)
+    ((by infer_instance))
   have hpmf :
       pmfProb ν (fun b : γ => p b.1) - pmfProb ν (fun b : γ => q b.1) ≤
         pmfProb ν (fun b : γ => r b.1) - pmfProb ν (fun b : γ => s b.1) := by
@@ -1446,7 +1446,7 @@
     simp [U]
   change (μ U).toReal ≤ ∑ i ∈ s, measureProb μ (fun a => p i a)
   rw [hset]
-  simpa [measureProb] using
+  simpa only [measureProb, Measure.real] using
     (measureReal_biUnion_finset_le (μ := μ) (s := s) (f := fun i => {a : α | p i a}))
 
 /-- First-order complement lower bound for finite intersections. -/
@@ -1507,7 +1507,7 @@
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
@@ -1488,7 +1488,7 @@
   have hmeasure_pos : 0 < μ σ := by
     by_contra hnot_pos
     have hmeasure_zero : μ σ = 0 := by
-      exact le_antisymm (le_of_not_gt hnot_pos) (zero_le _)
+      exact le_antisymm (le_of_not_gt hnot_pos) (zero_le)
     have hrestrict_zero : μ.restrict σ = 0 :=
       Measure.restrict_eq_zero.2 hmeasure_zero
     unfold singleStateTripTime at htime_pos
@@ -1542,7 +1542,7 @@
   have hmeasure_pos : 0 < μ σ := by
     by_contra hnot_pos
     have hmeasure_zero : μ σ = 0 := by
-      exact le_antisymm (le_of_not_gt hnot_pos) (zero_le _)
+      exact le_antisymm (le_of_not_gt hnot_pos) (zero_le)
     have hrestrict_zero : μ.restrict σ = 0 :=
       Measure.restrict_eq_zero.2 hmeasure_zero
     unfold singleStateTripTime at htime_pos
@@ -3779,7 +3779,7 @@
             (1 + arrivalRate * singleStateTripTime μ σ)))
         hw_integrable_added hadded_measurable hpointwise
     rw [integral_const_mul] at hmono
-    simpa [mul_assoc] using hmono
+    simpa [mul_assoc, singleStateTripTime, singleStateTripPayment] using hmono
   change
     renewalRewardRate arrivalRate
         (singleStateTripPayment μ w σ) (singleStateTripTime μ σ) ≤
@@ -3857,7 +3857,7 @@
             (1 + arrivalRate * singleStateTripTime μ σ)))
         hremoved_measurable hpointwise
     rw [integral_const_mul] at hmono
-    simpa [mul_assoc] using hmono
+    simpa [mul_assoc, singleStateTripTime, singleStateTripPayment] using hmono
   change
     renewalRewardRate arrivalRate
         (singleStateTripPayment μ w σ) (singleStateTripTime μ σ) ≤
@@ -8599,6 +8599,8 @@
 def dynamicMeasurableIncentiveCompatible (R : DynamicReward) : Prop :=
   dynamicMeasurableOptimal R acceptAllDynamicPolicy
 
+attribute [local simp] dynamicMeasurableIncentiveCompatible
+
 /--
 Full dynamic IC implies the source-domain measurable IC predicate by
 restricting the deviation class to feasible measurable policies.
@@ -10094,6 +10096,8 @@
 def ctmcStructuredSurgePrice
     (m z lambdaIJ lambdaJI : ℝ) : PricingFunction :=
   structuredSurgePrice m z (gn21SwitchProb lambdaIJ lambdaJI)
+
+attribute [local simp] ctmcStructuredSurgePrice
 
 /--
 Structured CTMC prices are integrable on a policy set whenever trip time and
@@ -11209,9 +11213,9 @@
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
@@ -11237,9 +11241,9 @@
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
@@ -11260,8 +11264,8 @@
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
@@ -13461,7 +13465,8 @@
   have hden_path :
       QiPath u * Tj + Qj * TiPath u ≠ 0 := by
     simpa [hQi_val, hTi_val] using hden
-  convert hnum.div hden_deriv hden_path using 1
+  unfold gn21AggregateDynamicReward
+  convert! hnum.div hden_deriv hden_path using 1
   rw [hQi_val, hWi_val, hTi_val]
   unfold gn21DerivativeSignKernel
   field_simp [hden]
@@ -13721,8 +13726,8 @@
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
@@ -13731,7 +13736,8 @@
   have hdiv :=
     hnum.div (hasDerivAt_id u) hu
   have hresp := hdiv.add_const c3
-  convert hresp using 1
+  unfold gn21Lemma7CanonicalResponse
+  convert! hresp using 1
   unfold gn21Lemma7CanonicalDerivativeNumerator
   simp [id]
   ring_nf
@@ -13750,8 +13756,8 @@
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
@@ -13777,11 +13783,12 @@
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
@@ -14148,6 +14155,8 @@
     exact sameStrictSign_of_pos_mul_left D.scale
       (gn21DerivativeSignKernel D.q D.u D.wi D.Qi D.Qj D.Ti D.Tj D.Wi D.Wj)
       D.scale_pos
+
+attribute [local simp] lemma6DerivativeFormulaCertificate_of_endpoint_data
 
 /-- Lemma 6 endpoint data include the promised analytic derivative statement. -/
 theorem paper_lemma6_endpoint_hasDerivAt_of_data
@@ -14785,6 +14794,8 @@
   derivative_eq_scaled_kernel := by
     field_simp [hden]
 
+attribute [local simp] lemma6EndpointDerivativeData_of_aggregate_paths
+
 /--
 Aggregate-path form of Lemma 6: once the endpoint derivatives of `Q_i`,
 `W_i`, and `T_i` are known, the derivative of the aggregate reward quotient
@@ -14934,6 +14945,8 @@
         ht_int ht_meas ht_cont using 1
       ring)
     rfl rfl rfl hden
+
+attribute [local simp] lemma6EndpointDerivativeData_of_interval_density_paths
 
 /--
 Interval-density form of Lemma 6: under the source density assumptions for a
@@ -17273,7 +17286,7 @@
 to the merged open interval in the paper's a.e. policy convention.
 -/
 theorem policyAlmostEverywhereEq_ioo_union_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {a b c : TripLength} (hab : a ≤ b) (hbc : b ≤ c) :
     policyAlmostEverywhereEq μ
       (Set.Ioo a b ∪ Set.Ioo b c) (Set.Ioo a c) := by
@@ -17313,7 +17326,7 @@
 to the merged right ray.
 -/
 theorem policyAlmostEverywhereEq_ioo_union_Ioi_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {a b : TripLength} (hab : a ≤ b) :
     policyAlmostEverywhereEq μ
       (Set.Ioo a b ∪ Set.Ioi b) (Set.Ioi a) := by
@@ -17328,7 +17341,7 @@
 Lemma 5 boundary-tail reduction.
 -/
 theorem policyAlmostEverywhereEq_bounded_union_positiveRightRay_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {a b : TripLength} (ha : 0 ≤ a) (hab : a ≤ b) :
     policyAlmostEverywhereEq μ
       (Set.Ioo a b ∪
@@ -17390,7 +17403,7 @@
 a.e. equal to the merged positive left ray.
 -/
 theorem policyAlmostEverywhereEq_positiveLeftRay_union_bounded_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {a b : TripLength} (ha : 0 ≤ a) (hab : a ≤ b) :
     policyAlmostEverywhereEq μ
       ((GN21GeneralizedIntervalComponent.positiveLeftRay a).policy ∪
@@ -17434,7 +17447,7 @@
 the full positive trip domain.
 -/
 theorem policyAlmostEverywhereEq_positiveLeftRightRay_touching
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (a : TripLength) :
     policyAlmostEverywhereEq μ
       ((GN21GeneralizedIntervalComponent.positiveLeftRay a).policy ∪
@@ -17452,7 +17465,7 @@
 by the merged interval, modulo the paper's a.e. endpoint convention.
 -/
 theorem lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -17500,7 +17513,7 @@
 Strict version of `lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path`.
 -/
 theorem lemma5_upper_endpoint_merge_reward_gt_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -17550,7 +17563,7 @@
 while the upper endpoint of one interval moves to the next lower endpoint.
 -/
 theorem lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17607,7 +17620,7 @@
 `lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path_with_context`.
 -/
 theorem lemma5_upper_endpoint_merge_reward_gt_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17668,7 +17681,7 @@
 paper's subcase iteration.
 -/
 theorem lemma5_upper_endpoint_merge_or_first_zero_reward_gt_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17744,7 +17757,7 @@
 stops at the first derivative sign change.
 -/
 theorem lemma5_upper_endpoint_merge_or_first_zero_exists_strict_improvement_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17793,7 +17806,7 @@
 with all other intervals held fixed.
 -/
 theorem lemma5_lower_endpoint_merge_reward_ge_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17849,7 +17862,7 @@
 Strict context-aware lower-endpoint merge step.
 -/
 theorem lemma5_lower_endpoint_merge_reward_gt_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17908,7 +17921,7 @@
 the last zero of the derivative proxy.  Both branches strictly improve reward.
 -/
 theorem lemma5_lower_endpoint_merge_or_last_zero_reward_gt_of_endpoint_path_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -17983,7 +17996,7 @@
 strict-local optimality arguments.
 -/
 theorem lemma5_lower_endpoint_merge_or_last_zero_exists_strict_improvement_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (hR_congr :
@@ -19045,7 +19058,7 @@
 strictly smaller endpoint complexity.
 -/
 theorem lemma5_twoBounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19096,7 +19109,7 @@
 `lemma5_twoBounded_upper_merge_step_of_endpoint_path`.
 -/
 theorem lemma5_twoBounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19149,7 +19162,7 @@
 lowering component count by one.
 -/
 theorem lemma5_withTwoBounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -19204,7 +19217,7 @@
 `lemma5_withTwoBounded_upper_merge_step_of_endpoint_path`.
 -/
 theorem lemma5_withTwoBounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -19260,7 +19273,7 @@
 components are replaced by one merged bounded interval.
 -/
 theorem lemma5_withTwoBounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -19315,7 +19328,7 @@
 `lemma5_withTwoBounded_lower_merge_step_of_endpoint_path`.
 -/
 theorem lemma5_withTwoBounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -19371,7 +19384,7 @@
 arbitrary ordered tail held fixed as context.
 -/
 theorem lemma5_list_bounded_bounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19434,7 +19447,7 @@
 Strict ordered-list upper-endpoint merge for the first two bounded components.
 -/
 theorem lemma5_list_bounded_bounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19497,7 +19510,7 @@
 Ordered-list lower-endpoint merge for the first two bounded components.
 -/
 theorem lemma5_list_bounded_bounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19560,7 +19573,7 @@
 Strict ordered-list lower-endpoint merge for the first two bounded components.
 -/
 theorem lemma5_list_bounded_bounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19800,7 +19813,7 @@
 right ray becomes one positive right ray.
 -/
 theorem lemma5_list_bounded_rightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19888,7 +19901,7 @@
 Strict ordered-list right-tail merge.
 -/
 theorem lemma5_list_bounded_rightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -19979,7 +19992,7 @@
 right-tail version of the source quasi-convex Subcase 1C move.
 -/
 theorem lemma5_list_bounded_rightRay_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20065,7 +20078,7 @@
 Strict ordered-list right-tail lower-endpoint merge.
 -/
 theorem lemma5_list_bounded_rightRay_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20154,7 +20167,7 @@
 source quasi-convex Subcase 1B move.
 -/
 theorem lemma5_list_leftRay_bounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20242,7 +20255,7 @@
 Strict ordered-list left-boundary upper-endpoint merge.
 -/
 theorem lemma5_list_leftRay_bounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20331,7 +20344,7 @@
 component becomes one larger positive left ray.
 -/
 theorem lemma5_list_leftRay_bounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20419,7 +20432,7 @@
 Strict ordered-list left-tail merge.
 -/
 theorem lemma5_list_leftRay_bounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20509,7 +20522,7 @@
 endpoint to the right ray.
 -/
 theorem lemma5_list_leftRightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20593,7 +20606,7 @@
 Strict ordered-list accept-all merge by moving the left ray's upper endpoint.
 -/
 theorem lemma5_list_leftRightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20919,7 +20932,7 @@
 peeled off the first component.
 -/
 theorem lemma5_list_second_bounded_bounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -20992,7 +21005,7 @@
 components.
 -/
 theorem lemma5_list_second_bounded_bounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21065,7 +21078,7 @@
 preserving one leading component and the tail.
 -/
 theorem lemma5_list_second_bounded_bounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21138,7 +21151,7 @@
 components.
 -/
 theorem lemma5_list_second_bounded_bounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21212,7 +21225,7 @@
 one positive right ray.
 -/
 theorem lemma5_list_second_bounded_rightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21299,7 +21312,7 @@
 Strict ordered-list right-tail merge for the second component.
 -/
 theorem lemma5_list_second_bounded_rightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21388,7 +21401,7 @@
 ray merge by moving the ray lower endpoint left.
 -/
 theorem lemma5_list_second_bounded_rightRay_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21473,7 +21486,7 @@
 Strict ordered-list right-tail lower-endpoint merge for the second component.
 -/
 theorem lemma5_list_second_bounded_rightRay_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (hR_congr :
       ∀ {σ τ : TripPolicy}, policyAlmostEverywhereEq μ σ τ →
@@ -21561,7 +21574,7 @@
 tail form.
 -/
 theorem lemma5_withBoundedRightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21645,7 +21658,7 @@
 Strict contextual right-tail merge move.
 -/
 theorem lemma5_withBoundedRightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21731,7 +21744,7 @@
 bounded interval's upper endpoint.
 -/
 theorem lemma5_withBoundedRightRay_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21813,7 +21826,7 @@
 Strict contextual right-tail lower-endpoint merge move.
 -/
 theorem lemma5_withBoundedRightRay_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21896,7 +21909,7 @@
 bounded interval merge into one larger positive left ray.
 -/
 theorem lemma5_withLeftRayBounded_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -21984,7 +21997,7 @@
 to the bounded interval's lower endpoint.
 -/
 theorem lemma5_withLeftRayBounded_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22070,7 +22083,7 @@
 Strict contextual left-boundary upper-endpoint merge move.
 -/
 theorem lemma5_withLeftRayBounded_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22156,7 +22169,7 @@
 Strict contextual left-boundary merge move.
 -/
 theorem lemma5_withLeftRayBounded_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22244,7 +22257,7 @@
 positive domain.
 -/
 theorem lemma5_withLeftRightRay_upper_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22327,7 +22340,7 @@
 endpoint right.
 -/
 theorem lemma5_withLeftRightRay_upper_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22410,7 +22423,7 @@
 left to the preceding left ray.
 -/
 theorem lemma5_withLeftRightRay_lower_merge_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -22493,7 +22506,7 @@
 endpoint left.
 -/
 theorem lemma5_withLeftRightRay_lower_merge_strict_step_of_endpoint_path
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : GN21GeneralizedIntervalPolicy)
     (hR_congr :
@@ -23083,7 +23096,7 @@
 under a nonatomic trip-length measure it is accept-all up to a null set.
 -/
 theorem acceptAllAlmostEverywhere_of_rejectsMiddleTrips_self_of_subsetAcceptAll
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     {σ : TripPolicy} {t : ℝ}
     (hshape : rejectsMiddleTrips t t σ)
     (hsub : σ ⊆ acceptAllPolicy) :
@@ -23104,7 +23117,7 @@
 single boundary trip length.
 -/
 theorem singleStateRenewalReward_rejectMiddleTripsPolicy_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ) (w : PricingFunction) (t : ℝ)
     (hw_integrable_acceptAll : IntegrableOn w acceptAllPolicy μ)
     (htime_integrable_acceptAll :
@@ -23140,7 +23153,7 @@
 coincident-cutoff middle-rejection shape.
 -/
 theorem singleStateRenewalReward_rejectsMiddleTrips_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ) (w : PricingFunction) (σ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σ)
     (hsub : σ ⊆ acceptAllPolicy)
@@ -23160,7 +23173,7 @@
 middle-rejection policy under a nonatomic trip-length measure.
 -/
 theorem gn21ExitWeightIntegral_rejectMiddleTripsPolicy_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate switchIJ switchJI t : ℝ)
     (hq_integrable_acceptAll :
       IntegrableOn
@@ -23199,7 +23212,7 @@
 middle-rejection policy under a nonatomic trip-length measure.
 -/
 theorem gn21ScaledStateTime_rejectMiddleTripsPolicy_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate t : ℝ)
     (htime_integrable_acceptAll :
       IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ) :
@@ -23233,7 +23246,7 @@
 middle-rejection policy under a nonatomic trip-length measure.
 -/
 theorem gn21ScaledStateEarning_rejectMiddleTripsPolicy_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ) (w : PricingFunction) (t : ℝ)
     (hw_integrable_acceptAll : IntegrableOn w acceptAllPolicy μ) :
     gn21ScaledStateEarning μ arrivalRate w (rejectMiddleTripsPolicy t t) =
@@ -23266,7 +23279,7 @@
 coincident-cutoff middle-rejection policy.
 -/
 theorem gn21ExitWeightIntegral_rejectsMiddleTrips_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate switchIJ switchJI : ℝ)
     (σ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σ)
@@ -23289,7 +23302,7 @@
 coincident-cutoff middle-rejection policy.
 -/
 theorem gn21ScaledStateTime_rejectsMiddleTrips_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ)
     (σ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σ)
@@ -23309,7 +23322,7 @@
 coincident-cutoff middle-rejection policy.
 -/
 theorem gn21ScaledStateEarning_rejectsMiddleTrips_self_eq_acceptAll_of_noAtoms
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (arrivalRate : ℝ) (w : PricingFunction)
     (σ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σ)
@@ -24633,7 +24646,7 @@
 theorem GN21WithDensityAcceptAllSupport.noAtoms
     {μ : Measure TripLength}
     (D : GN21WithDensityAcceptAllSupport μ) :
-    NoAtoms μ := by
+    NullSingletonClass μ := by
   rw [D.hμ]
   infer_instance
 
@@ -24828,7 +24841,7 @@
     (hshape : rejectsMiddleTrips t t σ)
     (hsub : σ ⊆ acceptAllPolicy) :
     acceptAllAlmostEverywhere μ σ := by
-  haveI : NoAtoms μ := D.noAtoms
+  haveI : NullSingletonClass μ := D.noAtoms
   exact
     acceptAllAlmostEverywhere_of_rejectsMiddleTrips_self_of_subsetAcceptAll
       μ hshape hsub
@@ -25651,7 +25664,7 @@
 -/
 theorem
     lemma5_strictlyIncreasing_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (response : TripLength → ℝ)
@@ -25875,7 +25888,7 @@
 -/
 theorem
     lemma5_strictlyDecreasing_gap_exists_strict_improvement_of_stopped_endpoint_paths_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (response : TripLength → ℝ)
@@ -26130,7 +26143,7 @@
 -/
 theorem
     lemma5_strictQuasiConvex_three_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (response : TripLength → ℝ)
@@ -26528,7 +26541,7 @@
 -/
 theorem
     lemma5_strictQuasiConcave_two_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (Rhat : SingleStateReward)
     (context : TripPolicy)
     (response : TripLength → ℝ)
@@ -28905,7 +28918,7 @@
 theorem Lemma5PositiveResponseShapeData.positive_zero_set_null
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ] :
+    (μ : Measure TripLength) [NullSingletonClass μ] :
     μ ({τ : TripLength | 0 < τ ∧ response τ = 0}) = 0 := by
   cases D with
   | positive hpositive =>
@@ -29018,7 +29031,7 @@
   policy_form :
     lemma5PolicyForm shape (lemma5PositiveResponsePolicy response)
   positive_zero_set_null :
-    ∀ (μ : Measure TripLength) [NoAtoms μ],
+    ∀ (μ : Measure TripLength) [NullSingletonClass μ],
       μ ({τ : TripLength | 0 < τ ∧ response τ = 0}) = 0
 
 /-- The existing analytic response-shape package implies the smaller policy-form package. -/
@@ -29245,7 +29258,7 @@
 theorem Lemma5PositiveResponsePolicyFormData.policyAlmostEverywhereEq_positiveResponse_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponsePolicyFormData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29294,7 +29307,7 @@
 theorem Lemma5PositiveResponsePolicyFormData.policyFormAlmostEverywhere_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponsePolicyFormData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29318,7 +29331,7 @@
 def Lemma5PositiveResponsePolicyFormData.feasiblePolicyFormAlmostEverywhere_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponsePolicyFormData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29348,7 +29361,7 @@
 def Lemma5PositiveResponsePolicyFormData.feasiblePolicyFormAlmostEverywhere_of_feasible_optimal
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponsePolicyFormData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29375,7 +29388,7 @@
 policy-form data instead of stronger analytic response-shape data.
 -/
 def paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (response : TripLength → ℝ) {shape : Lemma5DerivativeShape}
     (σ : TripPolicy)
     (D : Lemma5PositiveResponsePolicyFormData response shape)
@@ -29402,7 +29415,7 @@
 theorem Lemma5PositiveResponseShapeData.policyAlmostEverywhereEq_positiveResponse_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29451,7 +29464,7 @@
 theorem Lemma5PositiveResponseShapeData.policyFormAlmostEverywhere_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29478,7 +29491,7 @@
 def Lemma5PositiveResponseShapeData.feasiblePolicyFormAlmostEverywhere_of_candidate_le
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29507,7 +29520,7 @@
 theorem Lemma5PositiveResponseShapeData.policyFormAlmostEverywhere_of_feasible_optimal
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29537,7 +29550,7 @@
 def Lemma5PositiveResponseShapeData.feasiblePolicyFormAlmostEverywhere_of_feasible_optimal
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29566,7 +29579,7 @@
 the canonical Lemma 5 policy form, modulo null boundary sets.
 -/
 theorem paper_lemma5_fixed_response_policy_form_ae_of_response_shape
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (response : TripLength → ℝ) {shape : Lemma5DerivativeShape}
     (σ : TripPolicy)
     (D : Lemma5PositiveResponseShapeData response shape)
@@ -29591,7 +29604,7 @@
 kept explicit for downstream Theorem 4 endpoint moves.
 -/
 def paper_lemma5_fixed_response_feasible_policy_form_ae_of_response_shape
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (response : TripLength → ℝ) {shape : Lemma5DerivativeShape}
     (σ : TripPolicy)
     (D : Lemma5PositiveResponseShapeData response shape)
@@ -29620,7 +29633,7 @@
 theorem Lemma5PositiveResponseShapeData.marginalSetReward_lt_positiveResponsePolicy_of_not_policyFormAE
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     (D : Lemma5PositiveResponseShapeData response shape)
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (σ : TripPolicy)
     (hresponse_measurable : Measurable response)
     (hresponse_integrable_acceptAll :
@@ -29650,7 +29663,7 @@
 sets.
 -/
 theorem paper_lemma5_marginal_optimizer_replacement_ae_of_response_shape
-    (μ : Measure TripLength) [NoAtoms μ]
+    (μ : Measure TripLength) [NullSingletonClass μ]
     (response : TripLength → ℝ)
     (σ0 : TripPolicy) (shape : Lemma5DerivativeShape)
     (hresponse_measurable : Measurable response)
@@ -31327,6 +31340,8 @@
         lemma5MarginalSetReward_lt_positiveResponsePolicy_of_accepts_negative_mass
           μ response σ0 hresponse_measurable hresponse_integrable_acceptAll
           hσ0_measurable hσ0_subset hnegative
+
+attribute [local simp] lemma5MarginalOptimizerReplacementCertificate_positiveResponse
 
 /--
 Paper-facing fixed-response Lemma 5 endpoint: the positive-response policy is
@@ -36144,6 +36159,8 @@
             (dynamicStateReward R ρ 1) (ρ 1) sshape hsreplacement
             (dynamicStateReward_optimal_of_dynamicOptimal R hρ 1)⟩⟩
 
+attribute [local simp] theorem4ShapeDerivationCertificate_of_shape_replacement
+
 /--
 Theorem 4 all-optimal replacement certificate: the analytic Lemma 5 step is
 available for every dynamic optimum, but the caller does not need to choose a
@@ -37052,6 +37069,8 @@
           C.nonsurge_positive_form ρ hρ⟩,
         ⟨.positive, theorem4SurgeAllowedLemma5Shape_positive,
           C.surge_positive_form ρ hρ⟩⟩
+
+attribute [local simp] theorem4ShapeDerivationCertificate_of_accept_all_derivation
 
 /--
 When Lemma 9/10 force positive Lemma 5 forms for every optimal policy,
@@ -39461,7 +39480,7 @@
 accept-all in that state.
 -/
 theorem gn21MeasuredAggregateRewardPrimitives_rejectsMiddle_self_eq_acceptAll_left_of_noAtoms
-    (μI μJ : Measure TripLength) [NoAtoms μI]
+    (μI μJ : Measure TripLength) [NullSingletonClass μI]
     (arrivalI arrivalJ switchIJ switchJI : ℝ)
     (wI wJ : PricingFunction) (σI σJ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σI)
@@ -39492,7 +39511,7 @@
 accept-all in that state.
 -/
 theorem gn21MeasuredAggregateRewardPrimitives_rejectsMiddle_self_eq_acceptAll_right_of_noAtoms
-    (μI μJ : Measure TripLength) [NoAtoms μJ]
+    (μI μJ : Measure TripLength) [NullSingletonClass μJ]
     (arrivalI arrivalJ switchIJ switchJI : ℝ)
     (wI wJ : PricingFunction) (σI σJ : TripPolicy) (t : ℝ)
     (hshape : rejectsMiddleTrips t t σJ)
@@ -53011,7 +53030,7 @@
 -/
 def Theorem4AllMeasurableFixedResponseShapeData.to_feasible_ae_policy_forms
     {μ : Fin 2 → Measure TripLength} {R : DynamicReward}
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (C : Theorem4AllMeasurableFixedResponseShapeData μ R) :
     Theorem4AllMeasurableFeasibleAEPolicyFormData μ R where
   exists_optimal := C.exists_optimal
@@ -53053,7 +53072,7 @@
 Lemma 5 representative.
 -/
 def Lemma5FixedResponsePolicyFormFeasibleOptimalData.to_feasiblePolicyFormAlmostEverywhere
-    {μ : Measure TripLength} [NoAtoms μ]
+    {μ : Measure TripLength} [NullSingletonClass μ]
     {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
     {σ : TripPolicy}
     (D : Lemma5FixedResponsePolicyFormFeasibleOptimalData μ response shape σ)
@@ -53576,7 +53595,7 @@
 -/
 def Theorem4AllMeasurableFixedResponsePolicyFormData.to_feasible_ae_policy_forms
     {μ : Fin 2 → Measure TripLength} {R : DynamicReward}
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (C : Theorem4AllMeasurableFixedResponsePolicyFormData μ R) :
     Theorem4AllMeasurableFeasibleAEPolicyFormData μ R where
   exists_optimal := C.exists_optimal
@@ -53599,7 +53618,7 @@
 -/
 noncomputable def Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData.to_feasible_ae_policy_forms
     {μ : Fin 2 → Measure TripLength}
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     {arrival m z : Fin 2 → ℝ}
     {switch12 switch21 : ℝ}
     (D :
@@ -54287,7 +54306,7 @@
 -/
 def theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_fixed_response_policy_forms_and_representative_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -54363,7 +54382,7 @@
 -/
 def theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementExistenceCertificate_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -54437,7 +54456,7 @@
 -/
 def theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -54516,7 +54535,7 @@
 -/
 theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -54599,7 +54618,7 @@
 -/
 theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (switch12 switch21 : ℝ)
     (forms :
@@ -94881,7 +94900,7 @@
 -/
 def GN21Theorem3FeasibleAERepresentativeSourceData.of_fixed_response_policy_forms
     {μ : Fin 2 → Measure TripLength}
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     {arrival : Fin 2 → ℝ}
     {switch12 switch21 : ℝ}
     {m z : Fin 2 → ℝ}
@@ -95149,7 +95168,7 @@
 -/
 def theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_fixed_response_policy_forms
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (C :
@@ -95224,7 +95243,7 @@
 -/
 def Theorem3AcceptAllMeasurableFixedResponsePolicyFormSourceAssumptions.to_feasible_ae_representative_source_assumptions
     {μ : Fin 2 → Measure TripLength}
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     {arrival : Fin 2 → ℝ}
     {rho R1 R2 switch12 switch21 : ℝ}
     (A :
@@ -95259,7 +95278,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -95286,7 +95305,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -95501,7 +95520,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.to_source_data
     {μ : Fin 2 → Measure TripLength}
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     {arrival m z : Fin 2 → ℝ}
     {switch12 switch21 : ℝ}
     (D :
@@ -97498,7 +97517,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_by_policy_form_middle_cutoff_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -97974,7 +97993,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_cross_by_policy_form_middle_cutoff_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -98282,7 +98301,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_eq_middle_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -98619,7 +98638,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_eq_middle_cutoff_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -98992,7 +99011,7 @@
 -/
 def GN21Theorem3FixedResponsePolicyFormRejectedMassSourceData.of_fixed_state_eq_middle_reroute
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival m z : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (P :
@@ -99255,7 +99274,7 @@
 -/
 def theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_fixed_response_policy_form_rejected_mass
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (C :
@@ -99329,7 +99348,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_rejected_mass_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99354,7 +99373,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_rejected_mass_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99373,7 +99392,7 @@
 -/
 def theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_fixed_response_policy_form_rejected_mass_existence
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (R1 R2 switch12 switch21 : ℝ)
     (C :
@@ -99447,7 +99466,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_rejected_mass_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99472,7 +99491,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_rejected_mass_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99490,7 +99509,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99537,7 +99556,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99555,7 +99574,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99603,7 +99622,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99621,7 +99640,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99659,7 +99678,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99937,7 +99956,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -99987,7 +100006,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_reroute_existence_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -100058,7 +100077,7 @@
 /-- IC-only projection of the existence-based fixed-response common fixed-state equality route. -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_policy_form_eq_middle_reroute_existence_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -100253,7 +100272,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_eq_middle_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -100289,7 +100308,7 @@
 /-- Ratio-source version of the one-threshold fixed-response middle-reroute route. -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_eq_middle_reroute_existence_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -100341,7 +100360,7 @@
 /-- IC-only projection of the one-threshold fixed-response middle-reroute ratio route. -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_eq_middle_reroute_existence_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -100441,7 +100460,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -100480,7 +100499,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_reroute_existence_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -100532,7 +100551,7 @@
 /-- IC-only projection of the bracket-level one-threshold fixed-response ratio route. -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_eq_middle_reroute_existence_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -100842,7 +100861,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -100893,7 +100912,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_cutoff_reroute_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -101274,7 +101293,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_eq_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -101360,7 +101379,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -101401,7 +101420,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_eq_middle_cutoff_reroute_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -101460,7 +101479,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_cutoff_reroute_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -101520,7 +101539,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_cutoff_reroute_normalized_mass_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -101581,7 +101600,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_eq_middle_cutoff_reroute_normalized_mass_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -101637,7 +101656,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_cutoff_fixed_state_eq_normalized_mass_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -101693,7 +101712,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_eq_middle_cutoff_fixed_state_eq_normalized_mass_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -101749,7 +101768,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_cutoff_fixed_state_named_rate_normalized_mass_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -101805,7 +101824,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_eq_middle_cutoff_fixed_state_named_rate_normalized_mass_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -104160,7 +104179,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -104198,7 +104217,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -104262,7 +104281,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -104300,7 +104319,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -104320,7 +104339,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -104393,7 +104412,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -105301,7 +105320,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105339,7 +105358,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105403,7 +105422,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105441,7 +105460,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105505,7 +105524,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105543,7 +105562,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105610,7 +105629,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cutoff_branch_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105648,7 +105667,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_surge_cutoff_branch_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105668,7 +105687,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cutoff_branch_field_middle_cutoff_reroute_ratio_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -105791,7 +105810,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105829,7 +105848,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105882,7 +105901,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions_via_ordered
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -105900,7 +105919,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions_via_ordered
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106264,7 +106283,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106302,7 +106321,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106355,7 +106374,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions_via_ordered
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106373,7 +106392,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions_via_ordered
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106515,7 +106534,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_branch_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106533,7 +106552,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_branch_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106550,7 +106569,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_exact_one_threshold_branch_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106567,7 +106586,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_exact_one_threshold_branch_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106584,7 +106603,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_branch_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106670,7 +106689,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106709,7 +106728,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106773,7 +106792,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106811,7 +106830,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106875,7 +106894,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -106913,7 +106932,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_one_threshold_bracket_surge_cutoff_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -107048,7 +107067,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_bracket_branch_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -107066,7 +107085,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_bracket_branch_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -107083,7 +107102,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_exact_one_threshold_bracket_branch_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -107100,7 +107119,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_prices_of_fixed_response_exact_one_threshold_bracket_branch_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -107118,7 +107137,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_bracket_branch_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -112553,7 +112572,7 @@
 -/
 theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_reroute_source_assumptions
     (μ : Fin 2 → Measure TripLength)
-    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
+    [NullSingletonClass (μ 0)] [NullSingletonClass (μ 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
```

## GN21DriverSurgePricing/ProofInterface.lean

```diff
--- upstream/GN21DriverSurgePricing/ProofInterface.lean
+++ lean-4.34.1/GN21DriverSurgePricing/ProofInterface.lean
@@ -101,7 +101,7 @@
 canonical paper form for the derivative shape, up to null endpoint sets.
 -/
 theorem lemma5_fixed_response_feasible_policy_form_ae_of_response_shape
-    (mu : Measure TripLength) [NoAtoms mu]
+    (mu : Measure TripLength) [NullSingletonClass mu]
     (response : TripLength → ℝ) {shape : Lemma5DerivativeShape}
     (sigma : TripPolicy)
     (D : Lemma5PositiveResponseShapeData response shape)
@@ -1411,7 +1411,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_fixed_response_policy_form_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1467,7 +1467,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_eq_middle_reroute_existence_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1517,7 +1517,7 @@
 /-- IC projection of the bracket-level fixed-response middle-reroute route. -/
 theorem theorem3_structured_measurable_ic_of_bracket_eq_middle_reroute_existence_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1571,7 +1571,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_fixed_response_eq_middle_cutoff_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1624,7 +1624,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_one_threshold_eq_middle_cutoff_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1677,7 +1677,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_eq_middle_cutoff_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1731,7 +1731,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_eq_middle_cutoff_normalized_mass_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1783,7 +1783,7 @@
 -/
 theorem theorem3_structured_measurable_ic_of_bracket_eq_middle_cutoff_normalized_mass_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1838,7 +1838,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_eq_middle_cutoff_fixed_state_eq_normalized_mass_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1891,7 +1891,7 @@
 -/
 theorem theorem3_structured_measurable_ic_of_bracket_eq_middle_cutoff_fixed_state_eq_normalized_mass_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1946,7 +1946,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_eq_middle_cutoff_fixed_state_named_rate_normalized_mass_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -1999,7 +1999,7 @@
 -/
 theorem theorem3_structured_measurable_ic_of_bracket_eq_middle_cutoff_fixed_state_named_rate_normalized_mass_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -3776,7 +3776,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_one_threshold_surge_cutoff_branch_fields_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -3832,7 +3832,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_ordered_cross_fields
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
@@ -3852,7 +3852,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_ordered_cross_fields_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -3904,7 +3904,7 @@
 -/
 theorem theorem3_structured_measurable_ic_of_bracket_ordered_cross_fields_ratio_source
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (hR1_eq : R1 = rho * R2)
@@ -3957,7 +3957,7 @@
 -/
 theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_cross_fields
     (mu : Fin 2 → Measure TripLength)
-    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
+    [NullSingletonClass (mu 0)] [NullSingletonClass (mu 1)]
     (arrival : Fin 2 → ℝ)
     (rho R1 R2 switch12 switch21 : ℝ)
     (A :
```
