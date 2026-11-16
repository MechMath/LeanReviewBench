# Compatibility migration

Proof and import API compatibility only; root types and non-proof definitions are preserved. Local imports relocated to Main/dep.

```diff
--- FormalSLT/Covering/ContinuousDudleyUnitInterval.lean
+++ FormalSLT/Covering/ContinuousDudleyUnitInterval.lean
@@ -59,7 +59,7 @@
 theorem unitIntervalEntropyProfile_intervalIntegrable (a b : ℝ) :
     IntervalIntegrable unitIntervalEntropyProfile volume a b := by
   have hcont : Continuous unitIntervalEntropyProfile := by
-    simpa [unitIntervalEntropyProfile] using
+    exact
       (continuous_const.add (Real.continuous_exp.comp continuous_neg))
   exact hcont.intervalIntegrable a b
 
--- FormalSLT/Covering/UnitIntervalDudley.lean
+++ FormalSLT/Covering/UnitIntervalDudley.lean
@@ -1085,8 +1085,7 @@
   intro j hj
   simp at hj
   subst j
-  simpa [unitIntervalExplicitMeshNet, unitIntervalExplicitMeshIndex]
-    using unitIntervalHalfQuarterPair_card_gt_one
+  exact unitIntervalHalfQuarterPair_card_gt_one
 
 private theorem unitIntervalExplicitMeshNet_coverCount_le_15_m1 :
     ∀ j ∈ Finset.range 1,
@@ -1327,7 +1326,7 @@
       dist (N0.projection unitIntervalZero) unitIntervalOne ≤ N0.radius := by
     have h := N0.projection_dist_le unitIntervalOne
     rw [hcenter]
-    simpa [dist_comm] using h
+    simpa only [N0, unitIntervalRoundedDyadicGridNet_dist, unitIntervalRademacherLinearProcess, dist_comm] using h
   have hdist_le :
       dist unitIntervalZero unitIntervalOne ≤ N0.radius + N0.radius := by
     calc
@@ -1655,8 +1654,7 @@
   have hbase :=
     FiniteSubGaussianProcess.FiniteDyadicDudleyInstance.projected_dudley_bound
       unitIntervalRoundedDyadicGridDudleyInstance m
-  simpa [unitIntervalRoundedDyadicGridDudleyInstance,
-    unitIntervalRademacherLinearProcess] using hbase
+  exact hbase
 
 /-- Prefix-free finite-horizon rounded-dyadic-grid projected Dudley bound.
 
@@ -1727,7 +1725,7 @@
             unitIntervalRademacherLinearProcess.X false
               (unitIntervalQuarterMeshNet.center u.1)) := by
       unfold finiteSup
-      simpa [hval] using hle
+      simpa only [hval] using hle
     simpa [unitIntervalRademacherLinearSup] using hle0
   · let u1 : FiniteNet.ProjectedIndex unitIntervalQuarterMeshNet :=
       ⟨unitIntervalQuarterMeshNet.project unitIntervalOne, ⟨unitIntervalOne, rfl⟩⟩
@@ -1749,7 +1747,7 @@
             unitIntervalRademacherLinearProcess.X true
               (unitIntervalQuarterMeshNet.center u.1)) := by
       unfold finiteSup
-      simpa [hval] using hle
+      simpa only [hval] using hle
     simpa [unitIntervalRademacherLinearSup] using hle1
 
 /-- Explicit projected-quarter finite-net Dudley bound for the supplied
@@ -1823,7 +1821,7 @@
             unitIntervalRademacherLinearProcess.X false
               ((unitIntervalDyadicRoundedGridNet level).center u.1)) := by
       unfold finiteSup
-      simpa [hval] using hle
+      simpa only [hval] using hle
     simpa [unitIntervalRademacherLinearSup] using hle0
   · let u1 : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet level) :=
       ⟨(unitIntervalDyadicRoundedGridNet level).project unitIntervalOne,
@@ -1852,7 +1850,7 @@
             unitIntervalRademacherLinearProcess.X true
               ((unitIntervalDyadicRoundedGridNet level).center u.1)) := by
       unfold finiteSup
-      simpa [hval] using hle
+      simpa only [hval] using hle
     simpa [unitIntervalRademacherLinearSup] using hle1
 
 /-- Any rounded dyadic projected finite supremum is exactly the supplied
@@ -1887,7 +1885,7 @@
   terminalError := 0
   terminal_bound := by
     intro m ω
-    simpa [unitIntervalRoundedDyadicGridNet] using
+    simpa only [unitIntervalRoundedDyadicGridDudleyInstance, unitIntervalRoundedDyadicGridNetSequence, unitIntervalRoundedDyadicGridNet, add_zero] using
       unitIntervalRademacherLinearSup_le_projectedRoundedDyadicGridSup
         (m + 1) ω
 
@@ -1925,7 +1923,7 @@
             unitIntervalRademacherLinearProcess.X false
               ((unitIntervalDyadicRoundedGridNet 2).center u.1)) := by
       unfold finiteSup
-      simpa [hval] using hle
+      simpa only [hval] using hle
     simpa [unitIntervalRademacherLinearSup] using hle0
   · let u1 : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet 2) :=
       ⟨(unitIntervalDyadicRoundedGridNet 2).project unitIntervalOne,
@@ -1953,7 +1951,7 @@
             unitIntervalRademacherLinearProcess.X true
               ((unitIntervalDyadicRoundedGridNet 2).center u.1)) := by
       unfold finiteSup
-      simpa [hval] using hle
+      simpa only [hval] using hle
     simpa [unitIntervalRademacherLinearSup] using hle1
 
 /-- Rounded generic-dyadic-grid Dudley bound for the supplied nonzero supremum
@@ -2018,7 +2016,7 @@
             unitIntervalRademacherLinearProcess.X false
               ((unitIntervalDyadicRoundedGridNet 3).center u.1)) := by
       unfold finiteSup
-      simpa [hval] using hle
+      simpa only [hval] using hle
     simpa [unitIntervalRademacherLinearSup] using hle0
   · let u1 : FiniteNet.ProjectedIndex (unitIntervalDyadicRoundedGridNet 3) :=
       ⟨(unitIntervalDyadicRoundedGridNet 3).project unitIntervalOne,
@@ -2046,7 +2044,7 @@
             unitIntervalRademacherLinearProcess.X true
               ((unitIntervalDyadicRoundedGridNet 3).center u.1)) := by
       unfold finiteSup
-      simpa [hval] using hle
+      simpa only [hval] using hle
     simpa [unitIntervalRademacherLinearSup] using hle1
 
 /-- Rounded generic-dyadic-grid `m = 2` Dudley bound for the supplied nonzero
@@ -2099,9 +2097,7 @@
     FiniteSubGaussianProcess.FiniteDyadicDudleyInstance.suppliedSup_dudley_bound
       unitIntervalRoundedDyadicGridDudleyInstance
       unitIntervalRademacherLinearSupRoundedDyadicGridAdapter m
-  simpa [unitIntervalRoundedDyadicGridDudleyInstance,
-    unitIntervalRademacherLinearSupRoundedDyadicGridAdapter,
-    unitIntervalRademacherLinearProcess] using hbase
+  simpa only [unitIntervalRoundedDyadicGridDudleyInstance, unitIntervalRoundedDyadicGridNetSequence, unitIntervalRademacherLinearSupRoundedDyadicGridAdapter, add_zero] using hbase
 
 /-- Prefix-free arbitrary finite-horizon rounded-dyadic-grid Dudley bound for
 the supplied nonzero supremum.
--- FormalSLT/Covering/TotalBoundedDudley.lean
+++ FormalSLT/Covering/TotalBoundedDudley.lean
@@ -267,7 +267,7 @@
         ((dyadicChainingFiniteNetOfTotallyBoundedUniv
           (T := T) hT hradiusScale j).net.projection t) ≤
       dyadicChainingNetRadius radiusScale j := by
-  simpa using
+  exact
     (finiteNetOfTotallyBoundedUniv_covers
       (T := T) hT (dyadicChainingNetRadius_pos hradiusScale j) t)
 
--- FormalSLT/Covering/FiniteSubGaussianChaining.lean
+++ FormalSLT/Covering/FiniteSubGaussianChaining.lean
@@ -414,7 +414,7 @@
         (Finset.univ : Finset (FiniteNet.ProjectedIndex N)).sup'
           Finset.univ_nonempty
           (fun u : FiniteNet.ProjectedIndex N => Y (N.center u.1)) := by
-    simpa [u] using
+    simpa only [u] using
       Finset.le_sup'
         (fun u : FiniteNet.ProjectedIndex N => Y (N.center u.1))
         (Finset.mem_univ u)
@@ -1608,7 +1608,7 @@
       (s := (Finset.univ : Finset (I j)))
       (fun i : I j => P.X ω (right j i) - P.X ω (left j i))
       (Finset.mem_univ (select j t))
-    simpa [hleft j hj t, hright j hj t] using hsel
+    simpa only [hleft j hj t, hright j hj t] using hsel
   calc
     finiteExpectation P.weight
         (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t)))
@@ -1659,7 +1659,7 @@
       (s := (Finset.univ : Finset (I j)))
       (fun i : I j => P.X ω (right j i) - P.X ω (left j i))
       (Finset.mem_univ (select j t))
-    simpa [hleft j hj t, hright j hj t] using hsel
+    simpa only [hleft j hj t, hright j hj t] using hsel
   calc
     finiteExpectation P.weight
         (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t)))
@@ -1711,7 +1711,7 @@
       (s := (Finset.univ : Finset (I j)))
       (fun i : I j => P.X ω (right j i) - P.X ω (left j i))
       (Finset.mem_univ (select j u))
-    simpa [hleft j hj u, hright j hj u] using hsel
+    simpa only [hleft j hj u, hright j hj u] using hsel
   calc
     finiteExpectation P.weight
         (fun ω => finiteSup (fun u => P.X ω (π (j + 1) u) - P.X ω (π j u)))
@@ -1761,7 +1761,7 @@
       (s := (Finset.univ : Finset (I j)))
       (fun i : I j => P.X ω (right j i) - P.X ω (left j i))
       (Finset.mem_univ (select j u))
-    simpa [hleft j hj u, hright j hj u] using hsel
+    simpa only [hleft j hj u, hright j hj u] using hsel
   calc
     finiteExpectation P.weight
         (fun ω => finiteSup (fun u => P.X ω (π (j + 1) u) - P.X ω (π j u)))
@@ -1813,7 +1813,7 @@
       (s := (Finset.univ : Finset (I j)))
       (fun i : I j => P.X ω (right j i) - P.X ω (left j i))
       (Finset.mem_univ (select j t))
-    simpa [hleft j hj t, hright j hj t] using hsel
+    simpa only [hleft j hj t, hright j hj t] using hsel
   calc
     finiteExpectation P.weight
         (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t)))
@@ -1863,7 +1863,7 @@
       (s := (Finset.univ : Finset (I j)))
       (fun i : I j => P.X ω (right j i) - P.X ω (left j i))
       (Finset.mem_univ (select j t))
-    simpa [hleft j hj t, hright j hj t] using hsel
+    simpa only [hleft j hj t, hright j hj t] using hsel
   calc
     finiteExpectation P.weight
         (fun ω => finiteSup (fun t => P.X ω (π (j + 1) t) - P.X ω (π j t)))
@@ -1911,7 +1911,7 @@
       (fun pair : FiniteNet.ProjectionPair N₀ N₁ =>
         P.X ω (right pair) - P.X ω (left pair))
       (Finset.mem_univ (FiniteNet.projectionPairOf N₀ N₁ t))
-    simpa [left, right, FiniteNet.projection, FiniteNet.projectionPairOf] using hsel
+    simpa only [left, right, FiniteNet.projection, FiniteNet.projectionPairOf] using hsel
   calc
     finiteExpectation P.weight
         (fun ω => finiteSup
@@ -1977,7 +1977,7 @@
       (fun pair : FiniteNet.ProjectionPair N₀ N₁ =>
         P.X ω (right pair) - P.X ω (left pair))
       (Finset.mem_univ (FiniteNet.projectionPairOf N₀ N₁ t))
-    simpa [left, right, FiniteNet.projection, FiniteNet.projectionPairOf] using hsel
+    simpa only [left, right, FiniteNet.projection, FiniteNet.projectionPairOf] using hsel
   calc
     finiteExpectation P.weight
         (fun ω => finiteSup
--- FormalSLT/Rademacher/Massart.lean
+++ FormalSLT/Rademacher/Massart.lean
@@ -147,7 +147,7 @@
   have h_prod_bound :
       ∏ k : Fin n, ∑ b : Bool, Real.exp (t * (n : ℝ)⁻¹ * signOfBool b * ℓ i (z k))
         ≤ ∏ k : Fin n, (2 * Real.exp (t ^ 2 * (n : ℝ)⁻¹ ^ 2 * ℓ i (z k) ^ 2 / 2)) :=
-    Finset.prod_le_prod
+    Finset.prod_le_prod₀
       (fun k _ => Finset.sum_nonneg (fun b _ => le_of_lt (Real.exp_pos _)))
       (fun k _ => h_coord_bound k)
   -- Step 6: simplify (2^n)⁻¹ * ∏_k (2 * exp(c_k)).
```
