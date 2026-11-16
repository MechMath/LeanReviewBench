# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

The following exact diffs retain the recorded compatibility choices. Source hash and import-relocation checks do not prove global equivalence of the historical and modern library environments.

## EconCSLib/Foundations/Probability/Admissions.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/Admissions.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/Admissions.lean
@@ -294,8 +294,9 @@
     (m : AdmissionsModel Θ Ω) (value : Θ → ℝ) :
     admissionsSelectedWelfareMass m (fun _ : Ω => True) value = pmfExp m.prior value := by
   -- With universal admission, conditioning on signal has no effect on expected welfare.
-  simpa [admissionsSelectedWelfareMass, pmfIndicatorExp] using
-    (pmfKernelJointExp m.prior m.signalKernel (fun θ _ => value θ))
+  have h := pmfKernelJointExp m.prior m.signalKernel (fun θ _ => value θ)
+  simp only [pmfExp_const] at h
+  simpa only [admissionsSelectedWelfareMass, pmfIndicatorExp, ite_true, admissionsJointMass, pmfExp] using h
 
 theorem admissionsSelectedWelfareConditionalExp_of_false {Θ Ω : Type*}
     [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
@@ -438,9 +439,9 @@
           = pmfExp m.prior value := by
     have hfull :
         pmfExp (admissionsJointMass m) (fun a : Θ × Ω => value a.1) = pmfExp m.prior value := by
-      simpa [admissionsJointMass] using
-        (pmfKernelJointExp (prior := m.prior) (obs := m.signalKernel)
-          (f := fun θ _ => value θ))
+      have h := pmfKernelJointExp (prior := m.prior) (obs := m.signalKernel) (f := fun θ _ => value θ)
+      simp only [pmfExp_const] at h
+      simpa only [admissionsJointMass, pmfExp] using h
     unfold admissionsSelectedWelfareMass pmfIndicatorExp
     calc
       pmfExp (admissionsJointMass m) (fun a : Θ × Ω => if p a.2 then value a.1 else 0) +
```

## EconCSLib/Foundations/Probability/Gaussian.lean

```diff
--- upstream/EconCSLib/Foundations/Probability/Gaussian.lean
+++ lean-4.34.1/EconCSLib/Foundations/Probability/Gaussian.lean
@@ -490,7 +490,7 @@
   dsimp [mixtureTailMass]
   exact Finset.sum_le_sum (by
     intro g _
-    simpa using
+    simpa only [thresholdPassProb, mul_one] using
       mul_le_mul_of_nonneg_left
         (api.normalTail_le_one (law g) threshold)
         (hweight g))
```

## LG21TestOptionalPolicies/MainTheorems.lean

```diff
--- upstream/LG21TestOptionalPolicies/MainTheorems.lean
+++ lean-4.34.1/LG21TestOptionalPolicies/MainTheorems.lean
@@ -2762,7 +2762,7 @@
     lg21SourceDemographicallyFair S := by
   intro e
   rw [hAccess e, hNoAccess e]
-  simpa [lg21DemographicEstimateDistribution, lg21DemographicallyFair] using
+  simpa [lg21DemographicEstimateDistribution, lg21DemographicallyFair, DemographicallyFair] using
     demographicallyFair_of_observableFair baseProfile (hobs e)
 
 /--
@@ -5837,7 +5837,7 @@
     [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
     (m : LG21Model Θ ΩBase ΩTest) :
     lg21BaseMass m (fun _ : ΩBase => True) = pmfExp m.prior m.quality := by
-  simpa [lg21BaseMass] using
+  simpa [lg21BaseMass, lg21BaseModel] using
     (admissionsSelectionMass_of_true (m := lg21BaseModel m) (value := m.quality))
 
 theorem lg21_base_no_accept
@@ -5852,7 +5852,7 @@
     [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
     (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] :
     lg21BaseMass m (fun ω => ¬ p ω) = pmfExp m.prior m.quality - lg21BaseMass m p := by
-  simpa [lg21BaseMass] using
+  simpa [lg21BaseMass, lg21BaseModel] using
     (admissionsSelectedWelfareMass_of_compl (m := lg21BaseModel m) (p := p)
       (value := m.quality))
 
@@ -5934,7 +5934,7 @@
     [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
     (m : LG21Model Θ ΩBase ΩTest) :
     lg21TestMass m (fun _ : ΩTest => True) = pmfExp m.prior m.quality := by
-  simpa [lg21TestMass] using
+  simpa [lg21TestMass, lg21TestModel] using
     (admissionsSelectionMass_of_true (m := lg21TestModel m) (value := m.quality))
 
 theorem lg21_test_no_accept
@@ -5949,7 +5949,7 @@
     [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
     (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] :
     lg21TestMass m (fun ω => ¬ p ω) = pmfExp m.prior m.quality - lg21TestMass m p := by
-  simpa [lg21TestMass] using
+  simpa [lg21TestMass, lg21TestModel] using
     (admissionsSelectedWelfareMass_of_compl (m := lg21TestModel m) (p := p)
       (value := m.quality))
 
@@ -6031,7 +6031,7 @@
     [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
     (m : LG21Model Θ ΩBase ΩTest) :
     lg21BaseConditionalMass m (fun _ : ΩBase => True) = pmfExp m.prior m.quality := by
-  simpa [lg21BaseConditionalMass] using
+  simpa [lg21BaseConditionalMass, lg21BaseModel] using
     (admissionsSelectedWelfareConditionalExp_of_true (m := lg21BaseModel m) (value := m.quality))
 
 theorem lg21_test_conditional_universal_accept
@@ -6039,7 +6039,7 @@
     [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
     (m : LG21Model Θ ΩBase ΩTest) :
   lg21TestConditionalMass m (fun _ : ΩTest => True) = pmfExp m.prior m.quality := by
-  simpa [lg21TestConditionalMass] using
+  simpa [lg21TestConditionalMass, lg21TestModel] using
     (admissionsSelectedWelfareConditionalExp_of_true (m := lg21TestModel m) (value := m.quality))
 
 theorem lg21_base_conditional_of_compl
@@ -6049,7 +6049,7 @@
     lg21BaseConditionalMass m (fun ω => ¬ p ω) =
       (pmfExp m.prior m.quality - lg21BaseSelectionProb m p * lg21BaseConditionalMass m p) /
         lg21BaseSelectionProb m (fun ω => ¬ p ω) := by
-  simpa [lg21BaseConditionalMass, lg21BaseSelectionProb] using
+  simpa [lg21BaseConditionalMass, lg21BaseSelectionProb, lg21BaseModel] using
     (admissionsSelectedWelfareConditionalExp_of_compl (m := lg21BaseModel m) (p := p)
       (value := m.quality))
 
@@ -6072,7 +6072,7 @@
     lg21TestConditionalMass m (fun ω => ¬ p ω) =
       (pmfExp m.prior m.quality - lg21TestSelectionProb m p * lg21TestConditionalMass m p) /
         lg21TestSelectionProb m (fun ω => ¬ p ω) := by
-  simpa [lg21TestConditionalMass, lg21TestSelectionProb] using
+  simpa [lg21TestConditionalMass, lg21TestSelectionProb, lg21TestModel] using
     (admissionsSelectedWelfareConditionalExp_of_compl (m := lg21TestModel m) (p := p)
       (value := m.quality))
```
