# Lean 4.34.1 compatibility

Proof-only scalar-action expansion, order API and integral elaboration adjustments. Root types and non-proof definitions are unchanged. Local import identities are relocated to Main/dep.

```diff
--- FormalSLT/AnytimeValid/MixtureCS.lean
+++ FormalSLT/AnytimeValid/MixtureCS.lean
@@ -655,7 +655,7 @@
       integrable_subGammaExponentialProcess_omegaProd_uniformPrior
         (ν := μ) (X := X) (sigma2 := sigma2) (b := b)
         (lam0 := lam0) (lam1 := lam1) n hb hσ hlam0.le h01 hblam1 hX_meas hbound
-    simpa [mixtureExponentialProcess] using hprod.integral_prod_left
+    exact hprod.integral_prod_left
   · -- hM_int
     intro n
     exact integrable_subGammaExponentialProcess_prod_uniformPrior
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
```
