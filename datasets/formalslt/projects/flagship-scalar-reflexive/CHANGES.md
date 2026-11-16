# Compatibility migration

Proof and import API compatibility only; root types and non-proof definitions are preserved. Local imports relocated to Main/dep.

```diff
--- FormalSLT/AnytimeValid/VilleMaximalIneq.lean
+++ FormalSLT/AnytimeValid/VilleMaximalIneq.lean
@@ -76,7 +76,7 @@
   have hD : ∫ ω, stoppedValue M τ ω ∂μ ≤ ∫ ω, M 0 ω ∂μ := by
     have hsub : Submartingale (-M) 𝒢 μ := hsup.neg
     have hmono := hsub.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hτ_stop
-        (fun ω => zero_le _) hτ_le
+        (fun ω => bot_le) hτ_le
     -- E[stoppedValue (-M) σ] = -E[stoppedValue M σ] for any stopping time σ
     have key : ∀ σ : Ω → ℕ∞,
         ∫ ω, stoppedValue (-M) σ ω ∂μ = -∫ ω, stoppedValue M σ ω ∂μ := by
@@ -86,6 +86,7 @@
       rw [hfun, integral_neg]
     simp only [key] at hmono
     rw [stoppedValue_const] at hmono
+    simp only [Pi.neg_apply, integral_neg] at hmono
     linarith
   calc a * μ.real evt ≤ ∫ ω in evt, stoppedValue M τ ω ∂μ := hB
     _ ≤ ∫ ω, stoppedValue M τ ω ∂μ := hC
--- FormalSLT/Concentration/SharpMcDiarmid.lean
+++ FormalSLT/Concentration/SharpMcDiarmid.lean
@@ -256,7 +256,7 @@
   have hZindep : iIndepFun (fun i ω => X i ω - ∫ x, X i x ∂μ) μ := by
     have h := hindep.comp (fun i => fun x : ℝ => x - ∫ x, X i x ∂μ)
       (fun i => measurable_id.sub_const _)
-    simpa [Function.comp] using h
+    simpa only [Function.comp_def] using h
   have hengine := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
     hZindep (c := c) (s := s) hZsub ht
   refine hengine.trans (le_of_eq ?_)
--- FormalSLT/Concentration/SubGamma/Extractor.lean
+++ FormalSLT/Concentration/SubGamma/Extractor.lean
@@ -159,12 +159,12 @@
   have h_lin_eq : μ[fun ω => lam * X ω | m] =ᵐ[μ] fun ω => lam * (μ[X | m]) ω := by
     have := h_smul_lin
     -- `lam • X = fun ω => lam * X ω` by `Pi.smul_apply` + `smul_eq_mul`.
-    simpa [Pi.smul_apply, smul_eq_mul] using this
+    simpa only [Pi.smul_def, smul_eq_mul] using this
   have h_quad_eq :
       μ[fun ω => lam ^ 2 / K * X ω ^ 2 | m]
         =ᵐ[μ] fun ω => lam ^ 2 / K * (μ[fun ω => X ω ^ 2 | m]) ω := by
     have := h_smul_quad
-    simpa [Pi.smul_apply, smul_eq_mul] using this
+    simpa only [Pi.smul_def, smul_eq_mul] using this
   -- Translate `h_step1` / `h_step2` from `Pi.add` form to `μ[fun ω => …]` form.
   -- `(f + g) ω = f ω + g ω` is `Pi.add_apply`; for `condExp` the integrand is
   -- the function itself, and `(fun _ => 1) + g` is definitionally
--- FormalSLT/PACBayes/GaussianKL.lean
+++ FormalSLT/PACBayes/GaussianKL.lean
@@ -1,5 +1,6 @@
 import Mathlib.Analysis.SpecialFunctions.Log.Basic
 import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
+import Mathlib.MeasureTheory.Measure.WithDensity
 import Mathlib.Tactic
 
 /-!
--- FormalSLT/PACBayes/VitaleLemma.lean
+++ FormalSLT/PACBayes/VitaleLemma.lean
@@ -1,5 +1,5 @@
 import Mathlib.Data.Real.Basic
-import Mathlib.MeasureTheory.Measure.MeasureSpace
+import Mathlib.MeasureTheory.Measure.Basic
 import Mathlib.Tactic
 
 /-!
--- FormalSLT/Probability/BernsteinMGF.lean
+++ FormalSLT/Probability/BernsteinMGF.lean
@@ -62,6 +62,7 @@
       ((Continuous.sub Real.continuous_exp (by fun_prop)).continuousOn)
       (fun x _ => (hasDerivAt_expSub x).differentiableAt.differentiableWithinAt)
     intro x _
+    change 0 ≤ deriv (fun y : ℝ => Real.exp y - (1 + y + y ^ 2 / 2)) x
     rw [(hasDerivAt_expSub x).deriv]
     have := Real.add_one_le_exp x; linarith
   have h0 : (fun y => Real.exp y - (1 + y + y ^ 2 / 2)) 0 = 0 := by simp
@@ -76,6 +77,7 @@
       ((Continuous.sub Real.continuous_exp (by fun_prop)).continuousOn)
       (fun x _ => (hasDerivAt_expSub x).differentiableAt.differentiableWithinAt)
     intro x _
+    change 0 ≤ deriv (fun y : ℝ => Real.exp y - (1 + y + y ^ 2 / 2)) x
     rw [(hasDerivAt_expSub x).deriv]
     have := Real.add_one_le_exp x; linarith
   have h0 : (fun y => Real.exp y - (1 + y + y ^ 2 / 2)) 0 = 0 := by simp
--- FormalSLT/Probability/FiniteUnionBound.lean
+++ FormalSLT/Probability/FiniteUnionBound.lean
@@ -2,7 +2,7 @@
 import Mathlib.Algebra.Order.BigOperators.Group.Finset
 import Mathlib.Data.ENNReal.Basic
 import Mathlib.Data.Real.Basic
-import Mathlib.MeasureTheory.Measure.MeasureSpace
+import Mathlib.MeasureTheory.Measure.Basic
 import Mathlib.MeasureTheory.OuterMeasure.Basic
 
 open scoped BigOperators ENNReal
--- FormalSLT/Probability/IIDConcentration.lean
+++ FormalSLT/Probability/IIDConcentration.lean
@@ -103,7 +103,7 @@
     exact (hmeas t).neg
   have hYindep : iIndepFun Y μ := by
     have h := hindep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_id.neg)
-    simpa [Y, Function.comp] using h
+    simpa only [Y, Function.comp_def] using h
   have hYrange : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (-lossBound) 0 := by
     intro t
     filter_upwards [hbounded t] with ω hω
```
