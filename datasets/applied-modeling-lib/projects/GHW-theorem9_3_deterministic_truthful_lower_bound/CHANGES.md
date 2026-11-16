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

## EconCSLib/Foundations/Probability/FairCoin.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/FairCoin.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/FairCoin.lean
@@ -174,7 +174,7 @@
         (Ω := fun _ => Bool) (mΩ := fun _ => by infer_instance)
         (P := P) hμ (X := fun i : ι => (fun b : Bool => b))
         (mX := fun _ => measurable_id)
-  simpa [productMeasure, P] using hcoord.comp
+  simpa only [productMeasure, P, Function.comp_def] using hcoord.comp
     (fun _ b => if b = keep then (1 : ℝ) else 0)
     (fun _ => measurable_of_finite _)
```

## EconCSLib/MechanismDesign/Auctions/DigitalGoods.lean

```diff
--- upstream/EconCSLib/MechanismDesign/Auctions/DigitalGoods.lean
+++ lean-4.34.1/EconCSLib/MechanismDesign/Auctions/DigitalGoods.lean
@@ -1843,7 +1843,18 @@
       (highCount + lowCount : ℝ) := by
   classical
   unfold singlePriceRevenue
-  simp [twoValueBidProfile, hH_ge_one, Finset.sum_const, nsmul_eq_mul]
+  have hbid : ∀ i : TwoValueAgent highCount lowCount,
+      1 ≤ twoValueBidProfile H highCount lowCount i := by
+    intro i
+    cases i with
+    | inl _ => exact hH_ge_one
+    | inr _ => exact le_rfl
+  calc
+    _ = ∑ _ : TwoValueAgent highCount lowCount, (1 : ℝ) := by
+      apply Finset.sum_congr rfl
+      intro i _
+      exact if_pos (hbid i)
+    _ = _ := by simp [TwoValueAgent]
 
 theorem singlePriceRevenue_twoValueBidProfile_high
     {H highCount lowCount : ℕ}
```

## EconCSLib/MechanismDesign/Auctions/Position.lean

```diff
--- upstream/EconCSLib/MechanismDesign/Auctions/Position.lean
+++ lean-4.34.1/EconCSLib/MechanismDesign/Auctions/Position.lean
@@ -532,12 +532,12 @@
   classical
   have hfeasible :
       (PositionOutcome.zeroPaymentOutcome outcome.slotOf).FeasibleAssignment := by
-    simpa [PositionOutcome.zeroPaymentOutcome] using hout
+    exact hout
   have hmax :=
     (Classical.choose_spec
       (exists_welfareMaximizingSlotAssignment E reports)).2
       outcome.slotOf hfeasible
-  simpa [PositionOutcome.welfare, PositionOutcome.zeroPaymentOutcome] using hmax
+  exact hmax
 
 /--
 Canonical finite position-auction VCG mechanism: choose a feasible
@@ -575,11 +575,9 @@
       utility_eq_welfare_minus_tax := ?_
       tax_independent := ?_ }
   · intro reports
-    simpa [positionVCGMechanismOfSlotRule,
-      PositionOutcome.zeroPaymentOutcome] using hfeasible reports
+    exact hfeasible reports
   · intro reports outcome hout
-    simpa [positionVCGMechanismOfSlotRule,
-      PositionOutcome.zeroPaymentOutcome] using hmax reports outcome hout
+    exact hmax reports outcome hout
   · intro values reports i
     let chosen : PositionOutcome Bidder Slot :=
       PositionOutcome.zeroPaymentOutcome (slotRule reports)
@@ -633,7 +631,8 @@
             hmax reports (without.removeBidderSlot i) hremove_feasible
           rw [PositionOutcome.removeBidderSlot_welfare_eq_welfareExcept
             E without reports i] at hle
-          simpa [chosen, hchosen_welfare_reports] using hle
+          change positionVCGBenchmark E slotRule reports i ≤ chosen.welfare E reports at hle
+          rwa [hchosen_welfare_reports] at hle
         have htax_eq :
             positionVCGBenchmark E slotRule reports i =
               chosen.welfareExcept E reports i :=
@@ -899,12 +898,29 @@
   | ⟨1, _⟩ => 8
   | ⟨_, _⟩ => 1
 
+private theorem plb_gspValue0 : gspCounterexampleValues (0 : Fin 3) = 10 := rfl
+attribute [local simp] plb_gspValue0
+
+private theorem plb_gspValue1 : gspCounterexampleValues (1 : Fin 3) = 8 := rfl
+attribute [local simp] plb_gspValue1
+
+private theorem plb_gspValue2 : gspCounterexampleValues (2 : Fin 3) = 1 := rfl
+attribute [local simp] plb_gspValue2
+
+private theorem plb_gspBid0 : gspCounterexampleLowerBids (0 : Fin 3) = 7 := rfl
+attribute [local simp] plb_gspBid0
+
+private theorem plb_gspBid1 : gspCounterexampleLowerBids (1 : Fin 3) = 8 := rfl
+attribute [local simp] plb_gspBid1
+
+private theorem plb_gspBid2 : gspCounterexampleLowerBids (2 : Fin 3) = 1 := rfl
+attribute [local simp] plb_gspBid2
+
 theorem gspCounterexampleLowerBids_eq_update :
     gspCounterexampleLowerBids =
       Function.update gspCounterexampleValues (0 : Fin 3) 7 := by
   funext i
-  fin_cases i <;> norm_num [gspCounterexampleLowerBids,
-    gspCounterexampleValues, Function.update]
+  fin_cases i <;> norm_num [Function.update]
 
 /--
 Truthful GSP-style next-price outcome for values/bids `(10, 8, 1)`.
@@ -1018,14 +1034,12 @@
 theorem gspCounterexample_truthfulUtility_bidder0 :
     gspCounterexampleTruthfulOutcome.utility
       gspCounterexampleEnvironment gspCounterexampleValues (0 : Fin 3) = 2 := by
-  norm_num [PositionOutcome.utility, gspCounterexampleEnvironment,
-    gspCounterexampleValues, gspCounterexampleTruthfulOutcome]
+  norm_num [PositionOutcome.utility, gspCounterexampleEnvironment, gspCounterexampleTruthfulOutcome]
 
 theorem gspCounterexample_lowerBidUtility_bidder0 :
     gspCounterexampleLowerBidOutcome.utility
       gspCounterexampleEnvironment gspCounterexampleValues (0 : Fin 3) = 9 / 2 := by
-  norm_num [PositionOutcome.utility, gspCounterexampleEnvironment,
-    gspCounterexampleValues, gspCounterexampleLowerBidOutcome]
+  norm_num [PositionOutcome.utility, gspCounterexampleEnvironment, gspCounterexampleLowerBidOutcome]
 
 /--
 Concrete witness that GSP-style position auctions are not dominant-strategy
@@ -1044,9 +1058,7 @@
     PositionMechanism.utility gspCounterexampleEnvironment
       gspCounterexampleMechanism
       gspCounterexampleValues gspCounterexampleValues (0 : Fin 3) = 2 := by
-  norm_num [PositionMechanism.utility, gspCounterexampleMechanism,
-    PositionOutcome.utility, gspCounterexampleEnvironment,
-    gspCounterexampleValues, gspCounterexampleTruthfulOutcome]
+  norm_num [PositionMechanism.utility, gspCounterexampleMechanism, PositionOutcome.utility, gspCounterexampleEnvironment, gspCounterexampleTruthfulOutcome]
 
 theorem gspCounterexampleMechanism_lowerBidUtility_bidder0 :
     PositionMechanism.utility gspCounterexampleEnvironment
@@ -1054,10 +1066,7 @@
       gspCounterexampleValues
       (Function.update gspCounterexampleValues (0 : Fin 3) 7)
       (0 : Fin 3) = 9 / 2 := by
-  norm_num [PositionMechanism.utility, gspCounterexampleMechanism,
-    PositionOutcome.utility, gspCounterexampleEnvironment,
-    gspCounterexampleValues, gspCounterexampleLowerBidOutcome,
-    Function.update]
+  norm_num [PositionMechanism.utility, gspCounterexampleMechanism, PositionOutcome.utility, gspCounterexampleEnvironment, gspCounterexampleLowerBidOutcome, Function.update]
 
 /--
 Mechanism-level version of the GSP counterexample: truthful bidding is not a
@@ -1080,8 +1089,7 @@
       gsp3TwoSlotMechanism gspCounterexampleValues =
         gspCounterexampleTruthfulOutcome := by
     ext i <;> fin_cases i <;>
-      norm_num [gsp3TwoSlotMechanism, gspCounterexampleTruthfulOutcome,
-        gspCounterexampleValues, topBidder3, secondBidder3, thirdBidder3]
+      norm_num [gsp3TwoSlotMechanism, gspCounterexampleTruthfulOutcome, topBidder3, secondBidder3, thirdBidder3]
   rw [PositionMechanism.utility, hmech]
   exact gspCounterexample_truthfulUtility_bidder0
 
@@ -1097,8 +1105,7 @@
         gspCounterexampleLowerBidOutcome := by
     rw [← gspCounterexampleLowerBids_eq_update]
     ext i <;> fin_cases i <;>
-      norm_num [gsp3TwoSlotMechanism, gspCounterexampleLowerBidOutcome,
-        gspCounterexampleLowerBids, topBidder3, secondBidder3, thirdBidder3]
+      norm_num [gsp3TwoSlotMechanism, gspCounterexampleLowerBidOutcome, topBidder3, secondBidder3, thirdBidder3]
   rw [PositionMechanism.utility, hmech]
   exact gspCounterexample_lowerBidUtility_bidder0
```

## EconCSLib/MechanismDesign/Auctions/Combinatorial.lean

```diff
--- upstream/EconCSLib/MechanismDesign/Auctions/Combinatorial.lean
+++ lean-4.34.1/EconCSLib/MechanismDesign/Auctions/Combinatorial.lean
@@ -6536,7 +6536,7 @@
   have hlt_updated :
       (updated j).value <
         (updated j).bundleSize * (updated n).averageAmountPerGood := by
-    simpa [updated, singleMindedValueUpdate, hjn.symm] using hlt
+    simpa [updated, singleMindedValueUpdate, hjn.symm, SingleMindedBid.bundleSize] using hlt
   have havg :
       (updated j).averageAmountPerGood <
         (updated n).averageAmountPerGood :=
@@ -6567,7 +6567,7 @@
   have hlt_updated :
       (updated j).bundleSize * (updated n).averageAmountPerGood <
         (updated j).value := by
-    simpa [updated, singleMindedValueUpdate, hjn.symm] using hlt
+    simpa [updated, singleMindedValueUpdate, hjn.symm, SingleMindedBid.bundleSize] using hlt
   have havg :
       (updated n).averageAmountPerGood <
         (updated j).averageAmountPerGood :=
@@ -7358,7 +7358,7 @@
     have hnext_split :
         singleMindedGreedyFirstDeniedBecauseOfFromState
           bids acceptedWithJ base j = some n := by
-      simpa [acceptedWithJ,
+      simpa [acceptedWithJ, singleMindedGreedyNextDeniedFromSplit,
         singleMindedGreedyNextDeniedFromOrder_eq_split
           bids before base j hjbefore] using hnext_display
     have hnbase : n ∈ base :=
@@ -7602,7 +7602,7 @@
     have hbranch :=
       singleMindedAverageSomeThresholdBranch_of_accepted_update
         reports hreports i hs hbranchValue_nonneg (by
-          simpa [singleMindedAverageGreedyAcceptedMechanism] using hacc)
+          simpa [singleMindedAverageGreedyAcceptedMechanism, singleMindedGreedyAcceptedMechanismFromOrderOf] using hacc)
     simpa [singleMindedAverageGreedyAcceptedMechanism, hp] using hbranch
   · have hnone :
         singleMindedAverageGreedyCriticalThreshold reports i s = none := by
@@ -8068,7 +8068,7 @@
     exact
       singleMindedAverageGreedyCriticalThreshold_accepted_threshold
         reports hreports (by
-          simpa [singleMindedAverageGreedyAcceptedMechanism] using hacc)
+          simpa [singleMindedAverageGreedyAcceptedMechanism, singleMindedGreedyAcceptedMechanismFromOrderOf] using hacc)
 
 /--
 Build the domain-aware critical-value certificate for the greedy
@@ -8272,7 +8272,7 @@
     simpa [before] using (Finset.mem_filter.mp hjfilter').1
   have hjconflict : SingleMindedBidsConflict bids i j := by
     exact (Finset.mem_filter.mp (by
-      simpa [before, singleMindedGreedyConflictingAccepted] using hjfilter)).2
+      simpa [before, singleMindedGreedyConflictingAccepted, SingleMindedBidsConflict] using hjfilter)).2
   have hjfinal : j ∈ singleMindedGreedyAcceptedFromOrder bids order := by
     let afterStep : Finset Bidder := singleMindedGreedyStep bids before i
     have hfinal_eq :
```

## GHW01DigitalGoods/AuctionMainTheorems.lean

```diff
--- upstream/GHW01DigitalGoods/AuctionMainTheorems.lean
+++ lean-4.34.1/GHW01DigitalGoods/AuctionMainTheorems.lean
@@ -10653,7 +10653,7 @@
         unfold saleCount
         exact Finset.card_pos.mpr
           ⟨minWinner, by simpa [qWinners] using hminWinner_qWinner⟩
-      simpa using hcard_pos
+      exact Nat.succ_le_of_lt hcard_pos
     have hsingle_le_benchmark :
         singlePriceRevenue values q ≤
           finiteCandidateFixedPriceBenchmark values 1 := by
@@ -10761,7 +10761,7 @@
         unfold saleCount
         exact Finset.card_pos.mpr
           ⟨minWinner, by simpa [qWinners] using hminWinner_qWinner⟩
-      simpa using hcard_pos
+      exact Nat.succ_le_of_lt hcard_pos
     have hsingle_le_benchmark :
         singlePriceRevenue values q ≤
           finiteCandidateFixedPriceBenchmark values 1 := by
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

## GHW01DigitalGoods/FixedSizeSampling.lean

```diff
--- upstream/GHW01DigitalGoods/FixedSizeSampling.lean
+++ lean-4.34.1/GHW01DigitalGoods/FixedSizeSampling.lean
@@ -362,11 +362,11 @@
       HasDerivAt f (-1 + x + Real.exp (-x)) x := by
     intro x
     dsimp [f]
-    convert
+    convert!
       (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
         (((hasDerivAt_id x).pow 2).div_const 2)).sub
           ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)) using 1
-    all_goals simp [id]
+    all_goals simp [id] <;> rfl
   have hcont : ContinuousOn f (Set.Icc 0 δ) := by
     intro x hx
     exact (hfderiv x).continuousAt.continuousWithinAt
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

## EconCSLib/Foundations/Probability/RealDistribution.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/RealDistribution.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/RealDistribution.lean
@@ -1207,7 +1207,7 @@
         (by
           refine ⟨a + 1, by linarith, ?_⟩
           exact measure_ne_top μ (Ioc a (a + 1)))
-    simpa [h_inter_empty] using h
+    simpa only [h_inter_empty, Function.comp_def, measure_empty] using h
   have hreal :
       Tendsto (fun b => (μ (Ioc a b)).toReal) (𝓝[>] a) (𝓝 0) :=
     (ENNReal.tendsto_toReal (by simp)).comp hmeasure
```

## EconCSLib/Foundations/Probability/OrderStatistics.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/OrderStatistics.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/OrderStatistics.lean
@@ -1151,8 +1151,8 @@
 
 theorem ascendingOrderStatistic_mono {n : ℕ} (sample : Fin n → ℝ) :
     Monotone (ascendingOrderStatistic sample) := by
-  simpa [ascendingOrderStatistic, Function.comp_def] using
-    Tuple.monotone_sort sample
+  unfold ascendingOrderStatistic
+  convert! Tuple.monotone_sort sample using 1 <;> rfl
 
 theorem ascendingOrderStatistic_filter_card_eq
     {n : ℕ} (sample : Fin n → ℝ) (x : ℝ) :
@@ -1671,9 +1671,8 @@
 
 theorem reflectedSample_measurable (M : ℝ) {n : ℕ} :
     Measurable (fun sample : Fin n → ℝ => reflectedSample M sample) := by
-  refine measurable_pi_lambda _ ?_
-  intro i
-  exact measurable_const.sub (measurable_pi_apply i)
+  unfold reflectedSample
+  exact measurable_pi_iff.mpr (fun i => measurable_const.sub (measurable_pi_apply i))
 
 theorem reflectedAscendingOrderStatistic_measurable
     (M : ℝ) {n : ℕ} (rank : Fin n) :
@@ -1700,7 +1699,7 @@
       simp only [Fin.val_rev]
       omega
     have hsort := ascendingOrderStatistic_mono sample hrev
-    dsimp [ascendingOrderStatistic, reflectedSample, Function.comp_def, σ] at hsort ⊢
+    dsimp [ascendingOrderStatistic, reflectedSample, Function.comp_def, σ, Fin.revPerm] at hsort ⊢
     linarith
   have hsorted :
       (reflectedSample M sample) ∘ σ =
@@ -2984,7 +2983,8 @@
     fun sample x => reflectedBottomKRankCountLayer M k sample x
   have h_layer_integrable' :
       MeasureTheory.Integrable (Function.uncurry f) (μ.prod ν) := by
-    simpa [ν, f, Function.uncurry] using h_layer_integrable
+    unfold ν f
+    convert! h_layer_integrable using 1 <;> rfl
   have hpoint :
       (fun sample : Fin n → ℝ => reflectedBottomKSum M sample k) =ᵐ[μ]
         fun sample : Fin n → ℝ => ∫ x, f sample x ∂ν := by
@@ -3420,7 +3420,7 @@
     orderStatisticTopKSumFromMean
         (expectedOrderStatisticMeanSeq sampleMeasure) k a =
       expectedSampleTopKSum (sampleMeasure a) k := by
-  simpa [expectedOrderStatisticMeanSeq] using
+  simpa [orderStatisticTopKSumFromMean, expectedSampleOrderStatisticMean, expectedOrderStatisticMeanSeq, orderStatisticTopKSumFromMean, expectedSampleOrderStatisticMean] using
     expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
       (sampleMeasure a) k h_integrable
 
@@ -3445,7 +3445,7 @@
         orderStatisticTopKSumFromMean
           (expectedOrderStatisticMeanSeq sampleMeasure) k a =
       expectedReflectedBottomKSum M (sampleMeasure a) k := by
-  simpa [expectedOrderStatisticMeanSeq] using
+  simpa [orderStatisticTopKSumFromMean, expectedSampleOrderStatisticMean, expectedOrderStatisticMeanSeq, orderStatisticTopKSumFromMean, expectedSampleOrderStatisticMean] using
     expectedSampleOrderStatisticTopKEndpointLoss_eq_expectedReflectedBottomKSum
       M (sampleMeasure a) k h_order_integrable h_top_integrable
```

## GHW01DigitalGoods/Section11FixedSizeBridge.lean

```diff
--- upstream/GHW01DigitalGoods/Section11FixedSizeBridge.lean
+++ lean-4.34.1/GHW01DigitalGoods/Section11FixedSizeBridge.lean
@@ -49,8 +49,7 @@
     (Finset.univ : Finset Agent).powersetCard sampleSize
   let eventSamples : Finset (Finset Agent) := samples.filter event
   have hsamples_nonempty : samples.Nonempty := by
-    simpa [samples] using
-      Finset.powersetCard_nonempty.mpr (by simpa using hsize)
+    exact Finset.powersetCard_nonempty.mpr (by simpa only [Finset.card_univ] using hsize)
   letI : Nonempty (FixedSizeSampleSpace Agent sampleSize) :=
     Finset.nonempty_coe_sort.mpr hsamples_nonempty
   let eventSet : Finset (FixedSizeSampleSpace Agent sampleSize) :=
```

## GHW01DigitalGoods/RandomSamplingDirectional.lean

```diff
--- upstream/GHW01DigitalGoods/RandomSamplingDirectional.lean
+++ lean-4.34.1/GHW01DigitalGoods/RandomSamplingDirectional.lean
@@ -395,7 +395,7 @@
     have hnat : winners.card ≤ 3 * fixedSizeHitCount winners sample.1 := by
       exact_mod_cast hreal
     simpa [hcount, hsample_count] using hnat
-  simpa [winners] using le_trans htail htarget
+  exact le_trans htail htarget
 
 /-- The source Section 6 random-sampling auction for a fixed partition: bids on
 `sampleSide` determine the threshold and are rejected; only the opposite side
```

## GHW01DigitalGoods/BoundedSourceDefinitions.lean

```diff
--- upstream/GHW01DigitalGoods/BoundedSourceDefinitions.lean
+++ lean-4.34.1/GHW01DigitalGoods/BoundedSourceDefinitions.lean
@@ -109,8 +109,7 @@
   have hselected :
       boundedSupplyFixedPriceBenchmark bids capacity =
         candidateBoundedSupplyRevenue bids capacity i := by
-    simpa [i] using
-      (Classical.choose_spec
+    exact (Classical.choose_spec
         (exists_boundedSupplyBenchmarkBidder bids capacity))
   refine ⟨bids i, ?_⟩
   apply Finset.mem_filter.mpr
```

## GHW01DigitalGoods/PaperInterface.lean

```diff
--- upstream/GHW01DigitalGoods/PaperInterface.lean
+++ lean-4.34.1/GHW01DigitalGoods/PaperInterface.lean
@@ -834,7 +834,7 @@
   classical
   letI : Nonempty Agent := ⟨Classical.choose hhighest⟩
   have _hsource_attained : ∃ i : Agent, values i = h := hhighest
-  simpa [totalValue, fixedPriceBenchmark] using
+  exact
     paper_theorem4_1_finite_candidate_benchmark_exact_logb_of_two_le
       values hh_ge_two hvalue_ge_one hvalue_le_h
 
@@ -869,7 +869,7 @@
   intro Agent _ values h hvalues_nonneg hh_pos hmax hvalue_le_h hcard_ge_two
   classical
   letI : Nonempty Agent := ⟨Classical.choose hmax⟩
-  simpa [totalValue, fixedPriceBenchmark] using
+  exact
     paper_corollary4_2_fixed_price_lower_bound_exact_logb_of_card_two_le
       values hvalues_nonneg hh_pos hmax hvalue_le_h hcard_ge_two
 
@@ -915,7 +915,7 @@
     {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
     (side : Agent → Bool) (sampleSide : Bool) (minWinners : ℕ) :
     truthful (randomSamplingOptimalThresholdAuction side sampleSide minWinners) := by
-  simpa [truthful] using
+  exact
     randomSamplingOptimalThresholdAuction_truthful side sampleSide minWinners
 
 /-- The directional random-sampling auction is individually rational for every
@@ -1117,7 +1117,7 @@
       total ≤ 192 * (Real.logb 2 h + 2) *
         weightedPairingSourceOperationalExpectedRevenue values source := by
   have htotal_bid : total = totalBidValue values := by
-    simpa [totalValue, totalBidValue] using htotal
+    exact htotal
   have hh_lt_total : h < total := by
     nlinarith [hh_ge_one, hlarge]
   let source : WeightedPairingSourceProfile values :=
@@ -1209,11 +1209,11 @@
     (optimalThreshold_attains_fixedPriceBenchmark values hvalue_ge_one).2
   have hfixed_le_total_value : fixedPriceBenchmark values ≤ totalValue values := by
     rw [← hfixed_eq]
-    simpa [totalValue, totalBidValue] using
+    exact
       singlePriceRevenue_le_totalBidValue_of_nonneg values
         (optimalThreshold values) hvalue_nonneg
   have htotal_bid : total = totalBidValue values := by
-    simpa [totalValue, totalBidValue] using htotal
+    exact htotal
   have hfixed_le_total : fixedPriceBenchmark values ≤ total := by
     rw [htotal]
     exact hfixed_le_total_value
@@ -1949,7 +1949,7 @@
         (fun sample => boundedSinglePriceSamplingCompetitiveEvent sample.1
           sampleSize (Fintype.card Agent - sampleSize) capacity
           values beta gamma) := by
-  simpa [truthful, section11_singlePriceSamplingAuction] using
+  exact
     boundedSinglePriceSampling_fixedSize_combined_guarantee
       sampleSize capacity values hsample_lt hbeta hgamma hsuccess
       hsuccess_le_one hgood_probability
@@ -2025,7 +2025,7 @@
           (Nat.div_le_self _ _))
         (fun sample => boundedDualPriceSamplingCompetitiveEvent sample.1
           capacity values beta gamma) := by
-  simpa [truthful, section11_dualPriceSamplingAuction] using
+  exact
     boundedDualPriceSampling_fixedHalf_combined_guarantee
       capacity values hbeta hgamma hsuccess hsuccess_le_one
       hgood_probability
```
