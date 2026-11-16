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
 import Mathlib.Algebra.BigOperators.Ring.Finset
 import Mathlib.Algebra.Order.BigOperators.Group.Finset
```

## EconCSLib/MechanismDesign/Auctions/Combinatorial.lean

```diff
--- upstream/EconCSLib/MechanismDesign/Auctions/Combinatorial.lean
+++ lean-4.34.1/EconCSLib/MechanismDesign/Auctions/Combinatorial.lean
@@ -6539,7 +6539,7 @@
   have hlt_updated :
       (updated j).value <
         (updated j).bundleSize * (updated n).averageAmountPerGood := by
-    simpa [updated, singleMindedValueUpdate, hjn.symm] using hlt
+    simpa [updated, singleMindedValueUpdate, hjn.symm, SingleMindedBid.bundleSize] using hlt
   have havg :
       (updated j).averageAmountPerGood <
         (updated n).averageAmountPerGood :=
@@ -6570,7 +6570,7 @@
   have hlt_updated :
       (updated j).bundleSize * (updated n).averageAmountPerGood <
         (updated j).value := by
-    simpa [updated, singleMindedValueUpdate, hjn.symm] using hlt
+    simpa [updated, singleMindedValueUpdate, hjn.symm, SingleMindedBid.bundleSize] using hlt
   have havg :
       (updated n).averageAmountPerGood <
         (updated j).averageAmountPerGood :=
@@ -7361,7 +7361,7 @@
     have hnext_split :
         singleMindedGreedyFirstDeniedBecauseOfFromState
           bids acceptedWithJ base j = some n := by
-      simpa [acceptedWithJ,
+      simpa [acceptedWithJ, singleMindedGreedyNextDeniedFromSplit,
         singleMindedGreedyNextDeniedFromOrder_eq_split
           bids before base j hjbefore] using hnext_display
     have hnbase : n ∈ base :=
@@ -7605,7 +7605,7 @@
     have hbranch :=
       singleMindedAverageSomeThresholdBranch_of_accepted_update
         reports hreports i hs hbranchValue_nonneg (by
-          simpa [singleMindedAverageGreedyAcceptedMechanism] using hacc)
+          simpa [singleMindedAverageGreedyAcceptedMechanism, singleMindedGreedyAcceptedMechanismFromOrderOf] using hacc)
     simpa [singleMindedAverageGreedyAcceptedMechanism, hp] using hbranch
   · have hnone :
         singleMindedAverageGreedyCriticalThreshold reports i s = none := by
@@ -8071,7 +8071,7 @@
     exact
       singleMindedAverageGreedyCriticalThreshold_accepted_threshold
         reports hreports (by
-          simpa [singleMindedAverageGreedyAcceptedMechanism] using hacc)
+          simpa [singleMindedAverageGreedyAcceptedMechanism, singleMindedGreedyAcceptedMechanismFromOrderOf] using hacc)
 
 /--
 Build the domain-aware critical-value certificate for the LOS02 greedy
@@ -8275,7 +8275,7 @@
     simpa [before] using (Finset.mem_filter.mp hjfilter').1
   have hjconflict : SingleMindedBidsConflict bids i j := by
     exact (Finset.mem_filter.mp (by
-      simpa [before, singleMindedGreedyConflictingAccepted] using hjfilter)).2
+      simpa [before, singleMindedGreedyConflictingAccepted, SingleMindedBidsConflict] using hjfilter)).2
   have hjfinal : j ∈ singleMindedGreedyAcceptedFromOrder bids order := by
     let afterStep : Finset Bidder := singleMindedGreedyStep bids before i
     have hfinal_eq :
```
