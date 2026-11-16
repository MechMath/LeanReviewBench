# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

## Recorded migration rationale

# CAR-02 formal migration: f005a0fe7be71905a7bbe2f85b7ecd23e84a637f

The historical root `linearized_metric_carleson` and its header are byte-for-byte
unchanged. Its `hT` retains the selected implicit phase θ; this migration does
not add the blueprint's missing universal phase premise. The before snapshot
retains `toReal` and the after snapshot retains its absence.

Reproduce using `python3 migrate_297.py f005a0fe7be71905a7bbe2f85b7ecd23e84a637f` from `carleson-01`.
Exact source hashes, adapted files, patch, compile/extraction logs and status
are under `../f005a0fe7be71905a7bbe2f85b7ecd23e84a637f/migration-297/`. Scratch oleans are not archived inputs.

## Historical external definition retained

Pinned historical Mathlib commit `ff99cdaecce8cab2fcc3d3828ab7f79717fbf77a`
defines `eLpNorm` with the branches `p=0 → 0`, `p=∞ → eLpNormEssSup`, otherwise
`eLpNorm' f p.toReal μ`, with no measurability guard. Evidence:
`../../historical-boundary/ff99cdaecce8cab2fcc3d3828ab7f79717fbf77a-actual-Defs.lean` (SHA-256 `2da1905d3617dabbe87de839d2447848a07cb86dfabd7bc2e707c305889ae8e2`).

Pinned modern Mathlib adds a nonmeasurable infinity branch. We therefore retain
the historical formula as `MeasureTheory.legacy297Norm` in the added project
module `Carleson.Legacy297Norm`; references to the old bare `eLpNorm` in the
historical ENorm and WeakType modules map to that definition. `eLpNorm'` and
`eLpNormEssSup` are unchanged primitive definitions at the external boundary.
`MemLp` references map to `Legacy297MemLp`, the original conjunction of almost
everywhere strong measurability and finite historical norm. No root assumption
is strengthened. Checked helper theorems prove equality to the modern norm
under AEStronglyMeasurable and full equivalence of historical/modern MemLp.
The parent `migration/LegacyNormBridge.lean` independently checks the complete
bounded strong-type contract bridge: output measurability is already an explicit
conjunct, so replacing norms there preserves the root hypothesis.

The legacy norm is project source and is traversed by LeanTrace, rather than
hidden behind an external boundary. Definition preservation here means keeping
the historical formula; unconditional old/new norm equality is expressly false.

## Remaining mappings

- Newly upstreamed historical declarations are locally prefixed, retaining their
  original statements and proof bodies or repaired proofs. Exact names appear in
  the patch (`carleson_*`, `legacy297_*`). None are removed as duplicates.
- `WithFunctionDistance` changes from `def` to `abbrev` with the identical body
  `Θ X`. This changes reducibility only, resolving new elaborator transparency;
  its type, ball metrics and every root-reachable mathematical definition stay
  the same.
- `FunLike.coe_injective'` maps to field `coe_injective`; order/measure/set API
  names map to current equivalents; deprecated transitivity/multiplication proof
  invocations are reproved using current lemmas.
- Two ENorm instances gain derived `enorm_zero := rfl` fields required by the
  modern structure. No class axiom is added to the root.
- Generic scalar-action helper headers keep `IsBoundedSMul`. Their proof uses
  the proven local conversion `NormedDivisionRing.toNormSMulClass`; no stronger
  generic helper assumption is silently substituted.
- `gcongr only` changes tactic registration, not a proposition. Historical
  proofs are repaired; no new `sorry`, axiom, or proof stub is introduced.

## Validation and limits

All 8 original import-closure modules plus the added historical norm module
compile with Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Original pre-existing `sorry` occurrences remain, including the root proof; this
is statement extraction, not proof certification. The source-edit inventory
checks that each module's textual `sorry` count does not increase. Actual
LeanTrace export is recorded separately in the migration status and log.

This migration checks the explicit historical norm discrepancy and API repairs;
it is not a machine proof that every external Mathlib declaration has unchanged
semantics across the full version gap. The source-level alignment label is
independent of compilation and retains the explicit phase-quantifier discrepancy.


## Carleson/ToMathlib/Misc.lean

```diff
--- upstream/Carleson/ToMathlib/Misc.lean
+++ lean-4.34.1/Carleson/ToMathlib/Misc.lean
@@ -20,37 +20,7 @@
 section ENNReal
 
 lemma tsum_one_eq' {α : Type*} (s : Set α) : ∑' (_:s), (1 : ℝ≥0∞) = s.encard := by
-  if hfin : s.Finite then
-    have hfin' : Finite s := hfin
-    rw [tsum_def]
-    simp only [ENNReal.summable, ↓reduceDIte]
-    have hsup: support (fun (_ : s) ↦ (1 : ℝ≥0∞)) = Set.univ := by
-      ext i
-      simp only [mem_support, ne_eq, one_ne_zero, not_false_eq_true, mem_univ]
-    have hsupfin: (Set.univ : Set s).Finite := finite_univ
-    rw [← hsup] at hsupfin
-    rw [if_pos hsupfin, hfin.encard_eq_coe_toFinset_card]
-    simp only [ENat.toENNReal_coe]
-    rw [Finset.card_eq_sum_ones]
-    rw [finsum_eq_sum (fun (_ : s) ↦ (1 :ℝ≥0∞)) hsupfin]
-    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul, Nat.cast_inj]
-    apply Finset.card_bij (fun a _ => a.val)
-    · intro a
-      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
-        Subtype.coe_prop, imp_self]
-    · intro a _ a' _ heq
-      ext
-      exact heq
-    · intro a ha
-      use ⟨a,by
-        simp only [Finite.mem_toFinset] at ha
-        exact ha⟩
-      simp only [Finite.mem_toFinset, mem_support, ne_eq, one_ne_zero, not_false_eq_true,
-        exists_const]
-  else
-  have : Infinite s := infinite_coe_iff.mpr hfin
-  rw [ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num), Set.encard_eq_top_iff.mpr hfin]
-  simp only [ENat.toENNReal_top]
+  exact ENNReal.tsum_set_one s
 
 lemma ENNReal.tsum_const_eq' {α : Type*} (s : Set α) (c : ℝ≥0∞) :
     ∑' (_:s), (c : ℝ≥0∞) = s.encard * c := by
@@ -75,8 +45,8 @@
   rw [← coe_inv this, coe_inj, Real.toNNReal_inv, one_div]
 
 lemma ENNReal.sum_geometric_two_pow_neg_one : ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-n : ℤ) = 2 := by
-  conv_lhs => enter [1, n]; rw [← one_mul (n : ℤ), ← neg_mul, ← Nat.cast_one]
-  rw [ENNReal.sum_geometric_two_pow_toNNReal zero_lt_one]; norm_num
+  convert ENNReal.sum_geometric_two_pow_toNNReal zero_lt_one using 1 <;> norm_num
+
 
 lemma ENNReal.sum_geometric_two_pow_neg_two :
     ∑' (n : ℕ), (2 : ℝ≥0∞) ^ (-2 * n : ℤ) = ((4 : ℝ) / 3).toNNReal := by
@@ -98,7 +68,7 @@
 end ENNReal
 
 section Indicator
-attribute [gcongr] Set.indicator_le_indicator mulIndicator_le_mulIndicator_of_subset
+attribute [gcongr only] Set.indicator_le_indicator mulIndicator_le_mulIndicator_of_subset
 end Indicator
 
 
@@ -110,7 +80,7 @@
 lemma lintegral_Ioc_partition {a b : ℕ} {c : ℝ} {f : ℝ → ℝ≥0∞} (hc : 0 ≤ c) :
     ∫⁻ t in Ioc (a * c) (b * c), f t =
     ∑ l ∈ Finset.Ico a b, ∫⁻ t in Ioc (l * c) ((l + 1 : ℕ) * c), f t := by
-  rcases lt_or_le b a with h | h
+  rcases lt_or_ge b a with h | h
   · rw [Finset.Ico_eq_empty (by omega), Ioc_eq_empty (by rw [not_lt]; gcongr),
       setLIntegral_empty, Finset.sum_empty]
   induction b, h using Nat.le_induction with
@@ -120,7 +90,7 @@
     have li : a * c ≤ b * c := by gcongr
     rw [← Ioc_union_Ioc_eq_Ioc li (by gcongr; omega),
       lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
-      Nat.Ico_succ_right_eq_insert_Ico h, Finset.sum_insert Finset.right_not_mem_Ico,
+      Nat.Ico_succ_right_eq_insert_Ico h, Finset.sum_insert (by simp),
       add_comm (lintegral ..), ih]
 
 /-! ## Averaging -/
@@ -151,13 +121,13 @@
 lemma setLaverage_add_left' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
     {s : Set α} {f g : α → ENNReal} (hf : AEMeasurable f μ) :
     ⨍⁻ x in s, (f x + g x) ∂μ = ⨍⁻ x in s, f x ∂μ + ⨍⁻ x in s, g x ∂μ := by
-  simp_rw [setLaverage_eq, ENNReal.div_add_div_same, lintegral_add_left' hf.restrict]
+  simp_rw [setLAverage_eq, ENNReal.div_add_div_same, lintegral_add_left' hf.restrict]
 
 -- Named for consistency with `setLintegral_mono'`
 lemma setLaverage_mono' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
     {s : Set α} (hs : MeasurableSet s) {f g : α → ENNReal} (h : ∀ x ∈ s, f x ≤ g x) :
     ⨍⁻ x in s, f x ∂μ ≤ ⨍⁻ x in s, g x ∂μ := by
-  simp_rw [setLaverage_eq]
+  simp_rw [setLAverage_eq]
   exact ENNReal.div_le_div_right (setLIntegral_mono' hs h) (μ s)
 
 end MeasureTheory
@@ -175,17 +145,17 @@
   refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
   exact ENNReal.measurable_toReal.comp_aemeasurable hu.aemeasurable
 
-lemma laverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
+lemma carleson_laverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
     ⨍⁻ a, f a ∂μ ≤ ⨍⁻ a, g a ∂μ :=
   lintegral_mono_ae <| h.filter_mono <| Measure.ae_mono' Measure.smul_absolutelyContinuous
 
-@[gcongr]
-lemma setLAverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
+@[gcongr only]
+lemma carleson_setLAverage_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
     ⨍⁻ a in s, f a ∂μ ≤ ⨍⁻ a in s, g a ∂μ :=
-  laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self
+  carleson_laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self
 
 lemma setLaverage_const_le {c : ℝ≥0∞} : ⨍⁻ _x in s, c ∂μ ≤ c := by
-  simp_rw [setLaverage_eq, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
+  simp_rw [setLAverage_eq, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
     univ_inter, div_eq_mul_inv, mul_assoc]
   conv_rhs => rw [← mul_one c]
   gcongr
@@ -199,7 +169,7 @@
   ext; simp [ENNReal.toReal]
 
 theorem restrict_absolutelyContinuous : μ.restrict s ≪ μ :=
-  fun s hs ↦ Measure.restrict_le_self s |>.trans hs.le |>.antisymm <| zero_le _
+  fun s hs ↦ Measure.restrict_le_self s |>.trans hs.le |>.antisymm <| (by positivity)
 
 end MeasureTheory
 
@@ -309,7 +279,7 @@
 end Set.Finite
 
 lemma Real.self_lt_two_rpow (x : ℝ) : x < 2 ^ x := by
-  rcases lt_or_le x 0 with h | h
+  rcases lt_or_ge x 0 with h | h
   · exact h.trans (rpow_pos_of_pos zero_lt_two x)
   · calc
       _ < (⌊x⌋₊.succ : ℝ) := Nat.lt_succ_floor x
@@ -359,7 +329,7 @@
     norm_exp_ofReal_mul_I, one_mul, ← norm_neg, neg_sub, mul_comm]
 
 lemma norm_exp_I_mul_ofReal_sub_one_le {x : ℝ} : ‖exp (I * x) - 1‖ ≤ ‖x‖ := by
-  rw [norm_exp_I_mul_ofReal_sub_one]
+  rw [_root_.norm_exp_I_mul_ofReal_sub_one]
   calc
     _ = 2 * |Real.sin (x / 2)| := by simp
     _ ≤ 2 * |x / 2| := (mul_le_mul_iff_of_pos_left zero_lt_two).mpr Real.abs_sin_le_abs
@@ -404,7 +374,7 @@
 -- must be in mathlib but can't find it
 theorem indicator_const {c : ℝ} {s: Set X}
     (hs: MeasurableSet s) (h2s : volume s < ⊤) : Integrable (s.indicator (fun _ ↦ c)) :=
-  (integrable_indicator_iff hs).mpr <| integrableOn_const.mpr <| Or.inr h2s
+  (integrable_indicator_iff hs).mpr <| integrableOn_const h2s.ne
 
 end Integrable
 
@@ -457,7 +427,7 @@
     · simp [hi, μ₀]
 
 -- Analogous to `MeasureTheory.integral_smul_const` in Mathlib
-theorem average_smul_const {X : Type*} {E : Type*} [MeasurableSpace X]
+theorem carleson_average_smul_const {X : Type*} {E : Type*} [MeasurableSpace X]
     {μ : MeasureTheory.Measure X} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type*}
     [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E] (f : X → 𝕜) (c : E) :
     ⨍ (x : X), f x • c ∂μ = (⨍ (x : X), f x ∂μ) • c :=
```

## Carleson/ToMathlib/CoverByBalls.lean

```diff
--- upstream/Carleson/ToMathlib/CoverByBalls.lean
+++ lean-4.34.1/Carleson/ToMathlib/CoverByBalls.lean
@@ -44,7 +44,7 @@
   refine ⟨fun ⟨_, _, hs⟩ ↦ ?_, fun hs ↦ ?_⟩
   · simpa using hs
   · have h22 : s ⊆ ⋃ x ∈ (∅ : Finset X), ball x 0 := by
-      simp only [not_mem_empty, ball_zero, Set.iUnion_of_empty, Set.iUnion_empty]
+      simp only [Finset.notMem_empty, ball_zero, Set.iUnion_of_empty, Set.iUnion_empty]
       exact Set.subset_empty_iff.mpr hs
     use ∅, tsub_add_cancel_iff_le.mp rfl, h22
 
@@ -87,7 +87,7 @@
 lemma BallsCoverBalls.pow_mul {a : ℝ} {k : ℕ} (h : ∀ r, BallsCoverBalls X (a * r) r n) :
     BallsCoverBalls X (a^k * r) r (n^k) := by
   induction k with
-  | zero => simpa using fun x ↦ BallCoversSelf x r
+  | zero => simpa [BallsCoverBalls] using fun x ↦ BallCoversSelf x r
   | succ m h2 =>
     specialize h (r * a^m)
     rw [← mul_assoc, mul_comm, ← mul_assoc] at h
```

## Carleson/ToMathlib/DoublingMeasure.lean

```diff
--- upstream/Carleson/ToMathlib/DoublingMeasure.lean
+++ lean-4.34.1/Carleson/ToMathlib/DoublingMeasure.lean
@@ -1,3 +1,4 @@
+import Mathlib.Analysis.SpecialFunctions.Log.Base
 import Carleson.ToMathlib.CoverByBalls
 import Mathlib.Data.Real.StarOrdered
 import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
@@ -62,7 +63,7 @@
       _ ≤ A * μ (ball x r) := by gcongr; linarith
     by_contra H
     have : μ (ball x r) < 1 * μ (ball x r) := by
-      apply I.trans_lt (ENNReal.mul_lt_mul_right' H measure_ball_lt_top.ne (mod_cast hA))
+      apply I.trans_lt ((by gcongr; exact measure_ball_lt_top.ne; exact_mod_cast hA))
     simp at this
   rw [← measure_univ_eq_zero, ← iUnion_ball_nat x]
   exact measure_iUnion_null_iff.mpr fun i ↦ M ↑i (Nat.cast_nonneg' i)
@@ -80,7 +81,7 @@
   | zero => simp
   | succ m ih =>
       simp_rw [add_comm m 1, pow_add, pow_one, mul_assoc]
-      exact le_trans (measure_ball_two_le_same x _) (mul_le_mul_left' ih A)
+      exact le_trans (measure_ball_two_le_same x _) ((by gcongr))
 
 variable [ProperSpace X] [IsFiniteMeasureOnCompacts μ]
 
@@ -144,18 +145,18 @@
       (measure_real_ball_two_le_same ..) (zero_le_coe)
     _ = A ^ 2 * μ.real (ball x r) := by ring_nf
 
-lemma measure_ball_ne_top (x : X) (r : ℝ) : μ (ball x r) ≠ ∞ := measure_ball_lt_top.ne
+lemma carleson_measure_ball_ne_top (x : X) (r : ℝ) : μ (ball x r) ≠ ∞ := measure_ball_lt_top.ne
 
 lemma measure_ball_four_le_same' (x : X) (r : ℝ) :
     μ (ball x (4 * r)) ≤ A ^ 2 * μ (ball x r) := by
   have hfactor : (A ^ 2 : ℝ≥0∞) ≠ ⊤ := ne_of_beq_false rfl
-  rw [← ENNReal.ofReal_toReal (measure_ball_ne_top x (4 * r)),
-    ← ENNReal.ofReal_toReal (measure_ball_ne_top x r), ← ENNReal.ofReal_toReal hfactor,
+  rw [← ENNReal.ofReal_toReal (carleson_measure_ball_ne_top x (4 * r)),
+    ← ENNReal.ofReal_toReal (carleson_measure_ball_ne_top x r), ← ENNReal.ofReal_toReal hfactor,
     ← ENNReal.ofReal_mul]
   · exact ENNReal.ofReal_le_ofReal <| measure_ball_four_le_same x r
   · simp
 
-attribute [aesop (rule_sets := [finiteness]) safe apply] measure_ball_ne_top
+attribute [aesop (rule_sets := [finiteness]) safe apply] carleson_measure_ball_ne_top
 
 /-- The blow-up factor of repeatedly increasing the size of balls. -/
 def As (A : ℝ≥0) (s : ℝ) : ℝ≥0 := A ^ ⌈Real.logb 2 s⌉₊
@@ -201,8 +202,8 @@
 lemma measure_ball_le_same (x : X) {r s r' : ℝ} (hsp : 0 < s) (hs : r' ≤ s * r) :
     μ.real (ball x r') ≤ As A s * μ.real (ball x r) := by
   have hz := measure_ball_le_same' (μ := μ) x hsp hs
-  have hbr': μ (ball x r') ≠ ⊤ := measure_ball_ne_top x r'
-  have hbr: μ (ball x r) ≠ ⊤ := measure_ball_ne_top x r
+  have hbr': μ (ball x r') ≠ ⊤ := carleson_measure_ball_ne_top x r'
+  have hbr: μ (ball x r) ≠ ⊤ := carleson_measure_ball_ne_top x r
   have hAs : (As A s: ℝ≥0∞) ≠ ⊤ := coe_ne_top
   rw [← ENNReal.ofReal_toReal hbr,← ENNReal.ofReal_toReal hbr',
     ← ENNReal.ofReal_toReal hAs, ← ENNReal.ofReal_mul] at hz
@@ -215,7 +216,7 @@
 /-- Version of `measure_ball_le_same` without ceiling function. -/
 lemma measure_ball_le_same'' (x : X) {r t : ℝ} (ht : 0 < t) (h't : t ≤ 1) :
     μ.real (ball x r) ≤ A * t ^ (- Real.logb 2 A) * μ.real (ball x (t * r)) := by
-  rcases lt_or_le A 1 with hA | hA
+  rcases lt_or_ge A 1 with hA | hA
   · simp [eq_zero_of_isDoubling_lt_one μ hA]
   have : r = t⁻¹ * (t * r) := (eq_inv_mul_iff_mul_eq₀ ht.ne').mpr rfl
   apply (measure_ball_le_same x (inv_pos_of_pos ht) this.le).trans
@@ -255,7 +256,7 @@
     (h : dist x x' + r' ≤ s * r) :
     (μ (ball x' r')).toNNReal ≤ As A s * (μ (ball x r)).toNNReal := by
   simp only [← ENNReal.coe_le_coe, coe_mul, ENNReal.coe_toNNReal
-    (measure_ball_ne_top x r), ENNReal.coe_toNNReal (measure_ball_ne_top x' r')]
+    (carleson_measure_ball_ne_top x r), ENNReal.coe_toNNReal (carleson_measure_ball_ne_top x' r')]
   exact measure_ball_le_of_dist_le' hs h
 
 section
@@ -348,10 +349,10 @@
         ≤ μ (ball x (2 * (2 * r))) := μ.mono (closedBall_subset_ball (by linarith))
       _ ≤ A * μ (ball x (2 * r)) := measure_ball_two_le_same x (2 * r)
       _ ≤ A * (A * μ (ball x r)) := mul_le_mul_of_nonneg_left
-        (measure_ball_two_le_same x r) (zero_le _)
+        (measure_ball_two_le_same x r) (by positivity)
       _ = ↑(A ^ 2) * μ (ball x r) := by simp only [pow_two, coe_mul,mul_assoc]
       _ ≤ ↑(A ^ 2) * μ (closedBall x r) := mul_le_mul_of_nonneg_left
-        (μ.mono ball_subset_closedBall) (zero_le ((A ^ 2 : ℝ≥0) : ℝ≥0∞))
+        (μ.mono ball_subset_closedBall) (by positivity)
 end Metric
 
 section Normed
```

## Carleson/Legacy297Norm.lean

```diff
--- upstream/Carleson/Legacy297Norm.lean
+++ lean-4.34.1/Carleson/Legacy297Norm.lean
@@ -0,0 +1,28 @@
+import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
+noncomputable section
+open scoped ENNReal NNReal
+namespace MeasureTheory
+variable {α ε : Type*} [MeasurableSpace α] [ENorm ε]
+def legacy297Norm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
+  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f p.toReal μ
+@[simp] theorem legacy297Norm_exponent_zero (f : α → ε) (μ : Measure α) : legacy297Norm f 0 μ = 0 := by simp [legacy297Norm]
+@[simp] theorem legacy297Norm_exponent_top (f : α → ε) (μ : Measure α) : legacy297Norm f ∞ μ = eLpNormEssSup f μ := by simp [legacy297Norm]
+theorem legacy297Norm_eq_eLpNorm' {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} (h0 : p ≠ 0) (ht : p ≠ ∞) :
+    legacy297Norm f p μ = eLpNorm' f p.toReal μ := by simp [legacy297Norm, h0, ht]
+theorem legacy297Norm_nnreal_eq_eLpNorm' {f : α → ε} {p : ℝ≥0} {μ : Measure α} (h0 : p ≠ 0) :
+    legacy297Norm f p μ = eLpNorm' f p μ := by simp [legacy297Norm, h0]
+variable [TopologicalSpace ε]
+theorem legacy297Norm_eq_current {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} (hf : AEStronglyMeasurable f μ) :
+    legacy297Norm f p μ = eLpNorm f p μ := by simp [legacy297Norm, eLpNorm, hf]
+def Legacy297MemLp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
+  AEStronglyMeasurable f μ ∧ legacy297Norm f p μ < ∞
+theorem legacy297MemLp_iff {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} :
+    Legacy297MemLp f p μ ↔ MemLp f p μ := by
+  constructor
+  · intro h
+    change eLpNorm f p μ < ∞
+    rw [← legacy297Norm_eq_current h.1]
+    exact h.2
+  · intro h
+    exact ⟨h.aestronglyMeasurable, by simpa [legacy297Norm_eq_current h.aestronglyMeasurable] using (show eLpNorm f p μ < ∞ from h)⟩
+end MeasureTheory
```

## Carleson/ToMathlib/ENorm.lean

```diff
--- upstream/Carleson/ToMathlib/ENorm.lean
+++ lean-4.34.1/Carleson/ToMathlib/ENorm.lean
@@ -1,3 +1,4 @@
+import Carleson.Legacy297Norm
 import Mathlib.Analysis.Normed.Group.Basic
 import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
 import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
@@ -34,6 +35,7 @@
 attribute [simp] ENormedSpace.enorm_smul
 
 instance : ENormedSpace ℝ≥0∞ where
+  enorm_zero := rfl
   enorm := id
   enorm_eq_zero := by simp
   -- enorm_neg := by simp
@@ -45,6 +47,7 @@
   zero_smul := by simp
 
 instance : ENormedSpace ℝ≥0 where
+  enorm_zero := rfl
   enorm := ofNNReal
   add_smul r s x := by
     simp only [id_eq, smul_eq_mul]
@@ -74,25 +77,25 @@
 variable {ε ε' : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
   [TopologicalSpace ε'] [ContinuousENorm ε']
 
-lemma eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' {α : Type*} {m0 : MeasurableSpace α}
+lemma legacy297_eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' {α : Type*} {m0 : MeasurableSpace α}
     {μ : Measure α} {f : α → ε} {g : α → ε'} {c : ℝ≥0}
     (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) {p : ℝ} (hp : 0 < p) :
     eLpNorm' f p μ ≤ c • eLpNorm' g p μ := sorry
 
-lemma eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' {α : Type*}
+lemma legacy297_eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' {α : Type*}
   {m0 : MeasurableSpace α} {μ : Measure α} {f : α → ε} {g : α → ε'} {c : ℝ≥0}
   (h : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) : eLpNormEssSup f μ ≤ c • eLpNormEssSup g μ := sorry
 
-theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' {α : Type*} {m0 : MeasurableSpace α}
+theorem legacy297_eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' {α : Type*} {m0 : MeasurableSpace α}
     {μ : Measure α} {c : ℝ≥0} {f g : α → ε} (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) (p : ℝ≥0∞) :
-    eLpNorm f p μ ≤ c • eLpNorm g p μ := by
+    legacy297Norm f p μ ≤ c • legacy297Norm g p μ := by
   by_cases h0 : p = 0
   · simp [h0]
   by_cases h_top : p = ∞
   · rw [h_top]
-    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
-  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
-  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' h (ENNReal.toReal_pos h0 h_top)
+    exact legacy297_eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
+  simp_rw [legacy297Norm_eq_eLpNorm' h0 h_top]
+  exact legacy297_eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' h (ENNReal.toReal_pos h0 h_top)
 
 end ContinuousENorm
 
@@ -113,15 +116,15 @@
 variable {ε' : Type*} [TopologicalSpace ε'] [ENormedSpace ε']
 
 -- TODO: put next to MeasureTheory.eLpNorm_const_smul_le (which perhaps can stay)
-theorem eLpNorm_const_smul_le' {α : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞}
-  {μ : Measure α} {c : ℝ≥0} {f : α → ε}: eLpNorm (c • f) p μ ≤ ‖c‖ₑ * eLpNorm f p μ := by
-  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (p := p) ?_
+theorem legacy297_eLpNorm_const_smul_le' {α : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞}
+  {μ : Measure α} {c : ℝ≥0} {f : α → ε}: legacy297Norm (c • f) p μ ≤ ‖c‖ₑ * legacy297Norm f p μ := by
+  apply legacy297_eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (p := p) ?_
   filter_upwards with x using by simp [ENNReal.smul_def]
 
 -- TODO: put next to the unprimed version; perhaps both should stay
-lemma eLpNormEssSup_const_smul_le' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
+lemma legacy297_eLpNormEssSup_const_smul_le' {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
     {c : ℝ≥0} {f : α → ε} : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ := by
-  apply eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
+  apply legacy297_eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
   filter_upwards with x using by simp [ENNReal.smul_def]
 
 end ENormedSpace
```

## Carleson/ToMathlib/WeakType.lean

```diff
--- upstream/Carleson/ToMathlib/WeakType.lean
+++ lean-4.34.1/Carleson/ToMathlib/WeakType.lean
@@ -19,10 +19,10 @@
 
 -- todo: move/rename/and perhaps reformulate in terms of ‖.‖ₑ
 lemma ENNNorm_absolute_homogeneous {c : 𝕜} (z : E) : ofNNReal ‖c • z‖₊ = ↑‖c‖₊ * ↑‖z‖₊ :=
-  (toReal_eq_toReal_iff' coe_ne_top coe_ne_top).mp (norm_smul c z)
+  (by letI : NormSMulClass 𝕜 E := NormedDivisionRing.toNormSMulClass; exact (toReal_eq_toReal_iff' coe_ne_top coe_ne_top).mp (norm_smul c z))
 
 lemma enorm_absolute_homogeneous {c : 𝕜} (z : E) : ‖c • z‖ₑ = ‖c‖ₑ * ‖z‖ₑ :=
-  (toReal_eq_toReal_iff' coe_ne_top coe_ne_top).mp (norm_smul c z)
+  (by letI : NormSMulClass 𝕜 E := NormedDivisionRing.toNormSMulClass; exact (toReal_eq_toReal_iff' coe_ne_top coe_ne_top).mp (norm_smul c z))
 
 lemma ENNNorm_add_le (y z : E) : ofNNReal ‖y + z‖₊ ≤ ↑‖y‖₊ + ↑‖z‖₊ :=
   (toReal_le_toReal coe_ne_top coe_ne_top).mp (nnnorm_add_le ..)
@@ -61,16 +61,16 @@
   simp [hx]
 
 lemma eLpNorm_toReal_le {f : α → ℝ≥0∞} :
-    eLpNorm (ENNReal.toReal ∘ f) p μ ≤ eLpNorm f p μ := by
-  simp_rw [eLpNorm]
+    legacy297Norm (ENNReal.toReal ∘ f) p μ ≤ legacy297Norm f p μ := by
+  simp_rw [legacy297Norm]
   split_ifs
   · rfl
   · exact eLpNormEssSup_toReal_le
   · exact eLpNorm'_toReal_le toReal_nonneg
 
 lemma eLpNorm_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
-    eLpNorm (ENNReal.toReal ∘ f) p μ = eLpNorm f p μ := by
-  simp_rw [eLpNorm]
+    legacy297Norm (ENNReal.toReal ∘ f) p μ = legacy297Norm f p μ := by
+  simp_rw [legacy297Norm]
   split_ifs
   · rfl
   · exact eLpNormEssSup_toReal_eq hf
@@ -99,7 +99,7 @@
 def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
   μ { x | t < ‖f x‖ₑ }
 
-@[gcongr]
+@[gcongr only]
 lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ :=
   measure_mono fun _ a ↦ lt_of_le_of_lt h a
 
@@ -179,7 +179,7 @@
     ContinuousWithinAt (distribution f · μ) (Ioi t₀) t₀ := by
   rcases (eq_top_or_lt_top t₀) with t₀top | t₀nottop
   · rw [t₀top]
-    apply continuousWithinAt_of_not_mem_closure
+    apply continuousWithinAt_of_notMem_closure
     simp
   · unfold ContinuousWithinAt
     rcases (eq_top_or_lt_top (distribution f t₀ μ)) with db_top | db_not_top
@@ -211,7 +211,7 @@
           rw [db_zero] at h₂
           change Icc 0 ε (distribution f z μ)
           rw [nonpos_iff_eq_zero.mp h₂]
-          exact ⟨zero_le 0, zero_le ε⟩
+          exact ⟨(by positivity), (by positivity)⟩
       -- Case: 0 < distribution f t₀ μ
       · obtain ⟨n, wn⟩ :=
           select_neighborhood_distribution t₀ _ (ENNReal.sub_lt_self db_not_top.ne_top
@@ -306,20 +306,20 @@
   refine rpow_le_rpow ?_ p0'
   refine le_trans ?_ <| mul_meas_ge_le_lintegral₀ (hf.enorm'.pow_const p) (ofNNReal t ^ p)
   gcongr
-  exact setOf_subset_setOf.mpr (fun _ h ↦ h.le)
+  exact fun h ↦ h.le
 
 lemma wnorm_le_eLpNorm (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
-    wnorm f p μ ≤ eLpNorm f p μ := by
+    wnorm f p μ ≤ legacy297Norm f p μ := by
   by_cases h : p = ⊤
-  · simp [h, wnorm, eLpNorm]
+  · simp [h, wnorm, legacy297Norm]
   · have p0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne.symm
-    simpa [h, wnorm, eLpNorm, p0] using wnorm'_le_eLpNorm' hf (toReal_mono h hp)
+    simpa [h, wnorm, legacy297Norm, p0] using wnorm'_le_eLpNorm' hf (toReal_mono h hp)
 
 /-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
 def MemWℒp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
   AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞
 
-lemma MemLp.memWℒp (hp : 1 ≤ p) (hf : MemLp f p μ) : MemWℒp f p μ :=
+lemma Legacy297MemLp.memWℒp (hp : 1 ≤ p) (hf : Legacy297MemLp f p μ) : MemWℒp f p μ :=
   ⟨hf.1, wnorm_le_eLpNorm hf.1 hp |>.trans_lt hf.2⟩
 
 lemma MemWℒp_zero : ¬ MemWℒp f 0 μ := by
@@ -354,7 +354,7 @@
   by_cases hC_zero : C = 0
   · simp only [ENNReal.iSup_eq_zero, mul_eq_zero, ENNReal.rpow_eq_zero_iff, inv_neg'', C] at hC_zero
     specialize hC_zero 1
-    simp only [one_ne_zero, ENNReal.coe_one, toReal_nonneg.not_lt, and_false, or_false,
+    simp only [one_ne_zero, ENNReal.coe_one, not_lt_of_ge toReal_nonneg, and_false, or_false,
       false_or] at hC_zero
     exact measure_mono_null (setOf_subset_setOf.mpr fun x hx => hx ▸ one_lt_top) hC_zero.1
   by_contra h
@@ -377,7 +377,7 @@
         ENNReal.inv_div (Or.inr ofNat_ne_top) (Or.inr (NeZero.ne' 2).symm)]
   have h6 : μ A = 0 := by
     convert (fun hh ↦ ENNReal.half_lt_self hh (ne_top_of_le_ne_top (rpow_ne_top_of_nonneg
-      toReal_nonneg ((div_one C).symm ▸ h2.ne_top)) (h4 1))).mt h5.not_lt
+      toReal_nonneg ((div_one C).symm ▸ h2.ne_top)) (h4 1))).mt (not_lt_of_ge h5)
     tauto
   exact h h6
 
@@ -388,14 +388,14 @@
 and constant `c`.  -/
 def HasWeakType (T : (α → ε₁) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
     (c : ℝ≥0∞) : Prop :=
-  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ
+  ∀ f : α → ε₁, Legacy297MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * legacy297Norm f p μ
 
 /-- A weaker version of `HasWeakType`. -/
 def HasBoundedWeakType {α α' : Type*} [Zero ε₁]
     {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
     (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
-  ∀ f : α → ε₁, MemLp f p μ → eLpNorm f ∞ μ < ∞ → μ (support f) < ∞ →
-  AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * eLpNorm f p μ
+  ∀ f : α → ε₁, Legacy297MemLp f p μ → legacy297Norm f ∞ μ < ∞ → μ (support f) < ∞ →
+  AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * legacy297Norm f p μ
 
 /-- An operator has strong type (p, q) if it is bounded as an operator on `L^p → L^q`.
 `HasStrongType T p p' μ ν c` means that `T` has strong type (p, p') w.r.t. measures `μ`, `ν`
@@ -403,19 +403,19 @@
 def HasStrongType {α α' : Type*}
     {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
     (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
-  ∀ f : α → ε₁, MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ
+  ∀ f : α → ε₁, Legacy297MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ legacy297Norm (T f) p' ν ≤ c * legacy297Norm f p μ
 
 /-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
 w.r.t. the L^2 norm, but weaker in general. -/
 def HasBoundedStrongType {α α' : Type*} [Zero ε₁]
     {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
     (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
-  ∀ f : α → ε₁, MemLp f p μ → eLpNorm f ∞ μ < ∞ → μ (support f) < ∞ →
-  AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ
+  ∀ f : α → ε₁, Legacy297MemLp f p μ → legacy297Norm f ∞ μ < ∞ → μ (support f) < ∞ →
+  AEStronglyMeasurable (T f) ν ∧ legacy297Norm (T f) p' ν ≤ c * legacy297Norm f p μ
 
 /-! ### Lemmas about `HasWeakType` -/
 
-lemma HasWeakType.memWℒp (h : HasWeakType T p p' μ ν c) (hf₁ : MemLp f₁ p μ)
+lemma HasWeakType.memWℒp (h : HasWeakType T p p' μ ν c) (hf₁ : Legacy297MemLp f₁ p μ)
     (hc : c < ⊤ := by finiteness) : MemWℒp (T f₁) p' ν :=
   ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩
 
@@ -452,18 +452,18 @@
     exact this.union hf
 
 lemma hasWeakType_toReal_iff {T : (α → ε₁) → (α' → ℝ≥0∞)}
-    (hT : ∀ f, MemLp f p μ → ∀ᵐ x ∂ν, T f x ≠ ⊤) :
+    (hT : ∀ f, Legacy297MemLp f p μ → ∀ᵐ x ∂ν, T f x ≠ ⊤) :
     HasWeakType (T · · |>.toReal) p p' μ ν c ↔ HasWeakType T p p' μ ν c := by
   refine ⟨fun h ↦ fun f hf ↦ ?_, (·.toReal)⟩
   obtain ⟨h1, h2⟩ := h f hf
   refine ⟨?_, by rwa [← wnorm_toReal_eq (hT f hf)]⟩
   rwa [← aestronglyMeasurable_ennreal_toReal_iff]
-  refine .of_null <| measure_zero_iff_ae_nmem.mpr ?_
+  refine .of_null <| measure_eq_zero_iff_ae_notMem.mpr ?_
   filter_upwards [hT f hf] with x hx
   simp [hx]
 
 -- lemma comp_left [MeasurableSpace ε₂] {ν' : Measure ε₂} {f : ε₂ → ε₃} (h : HasWeakType T p p' μ ν c)
---     (hf : MemLp f p' ν') :
+--     (hf : Legacy297MemLp f p' ν') :
 --     HasWeakType (f ∘ T ·) p p' μ ν c := by
 --   intro u hu
 --   refine ⟨h u hu |>.1.comp_measurable hf.1, ?_⟩
@@ -471,7 +471,7 @@
 /-! ### Lemmas about `HasBoundedWeakType` -/
 
 lemma HasBoundedWeakType.memWℒp [Zero ε₁] (h : HasBoundedWeakType T p p' μ ν c)
-    (hf₁ : MemLp f₁ p μ) (h2f₁ : eLpNorm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞)
+    (hf₁ : Legacy297MemLp f₁ p μ) (h2f₁ : legacy297Norm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞)
     (hc : c < ⊤ := by finiteness) :
     MemWℒp (T f₁) p' ν :=
   ⟨(h f₁ hf₁ h2f₁ h3f₁).1, h f₁ hf₁ h2f₁ h3f₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩
@@ -482,8 +482,8 @@
 
 /-! ### Lemmas about `HasStrongType` -/
 
-lemma HasStrongType.memLp (h : HasStrongType T p p' μ ν c) (hf₁ : MemLp f₁ p μ)
-    (hc : c < ⊤ := by finiteness) : MemLp (T f₁) p' ν :=
+lemma HasStrongType.memLp (h : HasStrongType T p p' μ ν c) (hf₁ : Legacy297MemLp f₁ p μ)
+    (hc : c < ⊤ := by finiteness) : Legacy297MemLp (T f₁) p' ν :=
   ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩
 
 lemma HasStrongType.hasWeakType (hp' : 1 ≤ p')
@@ -495,21 +495,21 @@
   fun f hf ↦ ⟨(h f hf).1.ennreal_toReal, eLpNorm_toReal_le.trans (h f hf).2 ⟩
 
 lemma hasStrongType_toReal_iff {T : (α → ε₁) → (α' → ℝ≥0∞)}
-    (hT : ∀ f, MemLp f p μ → ∀ᵐ x ∂ν, T f x ≠ ⊤) :
+    (hT : ∀ f, Legacy297MemLp f p μ → ∀ᵐ x ∂ν, T f x ≠ ⊤) :
     HasStrongType (T · · |>.toReal) p p' μ ν c ↔ HasStrongType T p p' μ ν c := by
   refine ⟨fun h ↦ fun f hf ↦ ?_, (·.toReal)⟩
   obtain ⟨h1, h2⟩ := h f hf
   refine ⟨?_, by rwa [← eLpNorm_toReal_eq (hT f hf)]⟩
   rwa [← aestronglyMeasurable_ennreal_toReal_iff]
-  refine .of_null <| measure_zero_iff_ae_nmem.mpr ?_
+  refine .of_null <| measure_eq_zero_iff_ae_notMem.mpr ?_
   filter_upwards [hT f hf] with x hx
   simp [hx]
 
 /-! ### Lemmas about `HasBoundedStrongType` -/
 
 lemma HasBoundedStrongType.memLp [Zero ε₁] (h : HasBoundedStrongType T p p' μ ν c)
-    (hf₁ : MemLp f₁ p μ) (h2f₁ : eLpNorm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞)
-    (hc : c < ⊤ := by finiteness) : MemLp (T f₁) p' ν :=
+    (hf₁ : Legacy297MemLp f₁ p μ) (h2f₁ : legacy297Norm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞)
+    (hc : c < ⊤ := by finiteness) : Legacy297MemLp (T f₁) p' ν :=
   ⟨(h f₁ hf₁ h2f₁ h3f₁).1, h f₁ hf₁ h2f₁ h3f₁ |>.2.trans_lt <| mul_lt_top hc hf₁.2⟩
 
 lemma HasStrongType.hasBoundedStrongType [Zero ε₁] (h : HasStrongType T p p' μ ν c) :
@@ -525,7 +525,7 @@
 
 variable {f g : α → ε}
 
-@[gcongr]
+@[gcongr only]
 lemma distribution_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
     distribution f t μ ≤ distribution g t μ := by
   have h₀ : {x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ} ⊆ {x | ¬‖f x‖ₑ ≤ ‖g x‖ₑ} := fun x ↦ by
@@ -537,7 +537,7 @@
     _ = μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ}) := by rw [measure_mono_null h₀ h, add_zero]
     _ ≤ _ := by apply measure_mono; simp
 
-@[gcongr]
+@[gcongr only]
 lemma distribution_mono (h₁ : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) (h₂ : t ≤ s) :
     distribution f s μ ≤ distribution g t μ :=
   (distribution_mono_left h₁).trans (distribution_mono_right h₂)
@@ -558,7 +558,7 @@
       refine measure_mono fun x h ↦ ?_
       simp only [mem_union, mem_setOf_eq, Pi.add_apply] at h ⊢
       contrapose! h
-      exact (ENormedAddMonoid.enorm_add_le _ _).trans (add_le_add h.1 h.2)
+      exact (enorm_add_le _ _).trans (add_le_add h.1 h.2)
     _ ≤ _ := measure_union_le _ _
 
 end distribution
@@ -584,15 +584,17 @@
   unfold distribution
   congr with x
   simp only [Pi.smul_apply, mem_setOf_eq]
-  rw [← @ENNReal.mul_lt_mul_right (t / ‖c‖ₑ) _ (‖c‖ₑ) h₀ coe_ne_top,
-    enorm_absolute_homogeneous _, mul_comm, ENNReal.div_mul_cancel h₀ coe_ne_top]
+  rw [enorm_absolute_homogeneous _]
+  calc
+    t < ‖c‖ₑ * ‖f x‖ₑ ↔ (t / ‖c‖ₑ) * ‖c‖ₑ < ‖f x‖ₑ * ‖c‖ₑ := by rw [ENNReal.div_mul_cancel h₀ coe_ne_top, mul_comm ‖c‖ₑ]
+    _ ↔ _ := ENNReal.mul_lt_mul_iff_left h₀ coe_ne_top
 
 variable {𝕜 E' : Type*} [NormedRing 𝕜] [NormedAddCommGroup E'] [MulActionWithZero 𝕜 E'] [IsBoundedSMul 𝕜 E'] in
 lemma HasStrongType.const_smul {α α' : Type*} {_x : MeasurableSpace α} {_x' : MeasurableSpace α'}
     {T : (α → ε) → (α' → E')} {p p' : ℝ≥0∞} {μ : Measure α} {ν : Measure α'} {c : ℝ≥0∞}
     (h : HasStrongType T p p' μ ν c) (k : 𝕜) :
     HasStrongType (k • T) p p' μ ν (‖k‖ₑ * c) := by
-  refine fun f hf ↦ ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, eLpNorm_const_smul_le.trans ?_⟩
+  refine fun f hf ↦ ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, (show legacy297Norm (k • T f) p' ν ≤ ‖k‖ₑ * legacy297Norm (T f) p' ν by rw [legacy297Norm_eq_current (h f hf).1, legacy297Norm_eq_current ((h f hf).1.const_smul k)]; exact eLpNorm_const_smul_le).trans ?_⟩
   simp only [ENNReal.smul_def, smul_eq_mul, coe_mul, mul_assoc]
   gcongr
   exact (h f hf).2
@@ -639,10 +641,10 @@
   refine ⟨aestronglyMeasurable_const.smul (h f hf).1, ?_⟩
   calc wnorm ((k • T) f) p' ν
     _ ≤ ‖k‖ₑ * wnorm (T f) p' ν := by simp [wnorm_const_smul_le hp']
-    _ ≤ ‖k‖ₑ * (c * eLpNorm f p μ) := by
+    _ ≤ ‖k‖ₑ * (c * legacy297Norm f p μ) := by
       gcongr
       apply (h f hf).2
-    _ = (‖k‖ₑ * c) * eLpNorm f p μ := by simp [coe_mul, mul_assoc]
+    _ = (‖k‖ₑ * c) * legacy297Norm f p μ := by simp [coe_mul, mul_assoc]
 
 lemma HasWeakType.const_mul {α α' : Type*}
     {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} {T : (α → ε) → (α' → 𝕜)} {p p' : ℝ≥0∞}
@@ -667,7 +669,7 @@
           _ ≤ ‖L (f z)‖ₑ * ‖g z‖ₑ := ContinuousLinearMap.le_opENorm (L (f z)) (g z)
           _ ≤ ‖L‖ₑ * ‖f z‖ₑ * ‖g z‖ₑ :=
             mul_le_mul' (ContinuousLinearMap.le_opENorm L (f z)) (by rfl)
-      _ ≤ _ := mul_le_mul' (mul_le_mul_left' hz.1 ‖L‖ₑ) hz.2
+      _ ≤ _ := mul_le_mul' ((mul_le_mul_right hz.1 ‖L‖ₑ)) hz.2
   calc
     _ ≤ μ ({x | t < ‖f x‖ₑ} ∪ {x | s < ‖g x‖ₑ}) := measure_mono h₀
     _ ≤ _ := measure_union_le _ _
@@ -688,27 +690,27 @@
     ofReal_ne_top, not_false_eq_true, ← lintegral_const_mul', ← mul_assoc,
     ← ofReal_norm_eq_enorm, ofReal_mul, distribution, h2p] at this ⊢
   convert this using 1
-  refine setLIntegral_congr_fun measurableSet_Ioi (Eventually.of_forall fun x hx ↦ ?_)
+  refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ ?_)
   simp_rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hx)]
 
-/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`. -/
+/-- The layer-cake theorem, or Cavalieri's principle, written using `legacy297Norm`. -/
 lemma eLpNorm_pow_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ≥0} (hp : 0 < p) :
-    eLpNorm f p μ ^ (p : ℝ) =
+    legacy297Norm f p μ ^ (p : ℝ) =
     ∫⁻ t in Ioi (0 : ℝ), p * ENNReal.ofReal (t ^ ((p : ℝ) - 1)) * distribution f (.ofReal t) μ := by
   have h2p : 0 < (p : ℝ) := hp
-  simp_rw [eLpNorm_nnreal_eq_eLpNorm' hp.ne', eLpNorm', one_div, ← ENNReal.rpow_mul,
+  simp_rw [legacy297Norm_nnreal_eq_eLpNorm' hp.ne', eLpNorm', one_div, ← ENNReal.rpow_mul,
     inv_mul_cancel₀ h2p.ne', ENNReal.rpow_one, lintegral_norm_pow_eq_distribution hf h2p,
     ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal]
 
-/-- The layer-cake theorem, or Cavalieri's principle, written using `eLpNorm`, without
+/-- The layer-cake theorem, or Cavalieri's principle, written using `legacy297Norm`, without
     taking powers. -/
 lemma eLpNorm_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
-    eLpNorm f (.ofReal p) μ =
+    legacy297Norm f (.ofReal p) μ =
     (ENNReal.ofReal p  * ∫⁻ t in Ioi (0 : ℝ), distribution f (.ofReal t) μ *
         ENNReal.ofReal (t ^ (p - 1)) ) ^ p⁻¹ := by
-  unfold eLpNorm
+  unfold legacy297Norm
   split_ifs with sgn_p sz_p
-  · exact False.elim (not_le_of_lt hp (ofReal_eq_zero.mp sgn_p))
+  · exact False.elim (not_le.mpr hp (ofReal_eq_zero.mp sgn_p))
   · exact False.elim (coe_ne_top sz_p)
   · unfold eLpNorm'
     rw [toReal_ofReal (le_of_lt hp), one_div]
@@ -724,7 +726,12 @@
   have h2p : 0 < p + 1 := by linarith
   have h3p : 0 ≤ p + 1 := by linarith
   have h4p : p + 1 ≠ 0 := by linarith
-  simp [*, lintegral_norm_pow_eq_distribution, ← lintegral_const_mul', ← ofReal_mul, ← mul_assoc]
+  rw [lintegral_norm_pow_eq_distribution hf h2p, ← lintegral_const_mul']
+  · apply setLIntegral_congr_fun measurableSet_Ioi
+    intro t ht
+    simp only [add_sub_cancel_right]
+    rw [ENNReal.ofReal_inv_of_pos h2p, ENNReal.ofReal_mul h3p, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr h2p).ne' ENNReal.ofReal_ne_top, one_mul]
+  · exact ENNReal.ofReal_ne_top
 
 end BorelSpace
```

## Carleson/ToMathlib/Data/ENNReal.lean

```diff
--- upstream/Carleson/ToMathlib/Data/ENNReal.lean
+++ lean-4.34.1/Carleson/ToMathlib/Data/ENNReal.lean
@@ -15,14 +15,14 @@
 attribute [simp] ofReal_of_nonpos
 -- protect ENNReal.mul_le_mul_left
 
-theorem ofReal_inv_le {x : ℝ} : ENNReal.ofReal x⁻¹ ≤ (ENNReal.ofReal x)⁻¹ := by
-  obtain hx|hx := lt_or_le 0 x <;> simp [ofReal_inv_of_pos, hx]
+theorem legacy297_ofReal_inv_le {x : ℝ} : ENNReal.ofReal x⁻¹ ≤ (ENNReal.ofReal x)⁻¹ := by
+  obtain hx|hx := lt_or_ge 0 x <;> simp [ofReal_inv_of_pos, hx]
 
-theorem ofReal_div_le {x y : ℝ} (hy : 0 ≤ y) :
+theorem legacy297_ofReal_div_le {x y : ℝ} (hy : 0 ≤ y) :
     ENNReal.ofReal (x / y) ≤ ENNReal.ofReal x / ENNReal.ofReal y := by
   simp_rw [div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy)]
   gcongr
-  exact ofReal_inv_le
+  exact legacy297_ofReal_inv_le
 
 lemma coe_biSup {f : ι → ℝ≥0} (hf : BddAbove (range f)) :
     ⨆ x ∈ s, f x = ⨆ x ∈ s, (f x : ℝ≥0∞) := by
@@ -46,7 +46,7 @@
   · refine le_antisymm ?_ (iSup₂_le fun a ma => add_le_add (le_biSup _ ma) (le_biSup _ ma))
     refine biSup_add_biSup_le hs hs fun i hi j hj => ?_
     obtain ⟨k, mk, hk⟩ := h i hi j hj
-    exact hk.trans <| le_iSup₂_of_le k mk fun a za ↦ ⟨a, za, le_rfl⟩
+    exact hk.trans <| le_iSup₂_of_le k mk le_rfl
 
 -- unused
 lemma finsetSum_biSup {f : α → ι → ℝ≥0∞}
@@ -69,7 +69,7 @@
   | empty => simp
   | cons a t ha ihs =>
     simp only [Finset.sum_cons]
-    exact biSup_add_le_add_biSup.trans (add_le_add_left ihs _)
+    exact biSup_add_le_add_biSup.trans (add_le_add_right ihs _)
 
 variable {E : Type*} [SeminormedAddCommGroup E]
 
@@ -79,7 +79,7 @@
   | empty => simp
   | cons a t ha ihs =>
     simp only [Finset.sum_cons]
-    exact (edist_add_add_le _ _ _ _).trans (add_le_add_left ihs _)
+    exact (edist_add_add_le _ _ _ _).trans (add_le_add_right ihs _)
 
 /-- The reverse triangle inequality for `enorm`. -/
 -- TODO: does a seminormed abelian additive group also have an ENormedAddMonoid structure?
```

## Carleson/Defs.lean

```diff
--- upstream/Carleson/Defs.lean
+++ lean-4.34.1/Carleson/Defs.lean
@@ -66,12 +66,12 @@
 instance : Coe (Θ X) C(X, 𝕜) := ⟨FunctionDistances.coeΘ⟩
 instance : FunLike (Θ X) X 𝕜 where
   coe := fun f ↦ (f : C(X, 𝕜))
-  coe_injective' _ _ hfg := FunctionDistances.coeΘ_injective fun x ↦ congrFun hfg x
+  coe_injective _ _ hfg := FunctionDistances.coeΘ_injective fun x ↦ congrFun hfg x
 instance : ContinuousMapClass (Θ X) X 𝕜 := ⟨fun f ↦ (f : C(X, 𝕜)).2⟩
 
 set_option linter.unusedVariables false in
 @[nolint unusedArguments]
-def WithFunctionDistance (x : X) (r : ℝ) := Θ X
+abbrev WithFunctionDistance (x : X) (r : ℝ) := Θ X
 
 variable {x : X} {r : ℝ}
 
@@ -137,7 +137,7 @@
 
 export CompatibleFunctions (localOscillation_le_cdist cdist_mono cdist_le le_cdist)
 
-lemma dist_congr [FunctionDistances 𝕜 X] {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ X}
+lemma legacy297_dist_congr [FunctionDistances 𝕜 X] {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ X}
     (e₁ : x₁ = x₂) (e₂ : r₁ = r₂) : dist_{x₁, r₁} f g = dist_{x₂, r₂} f g := by congr
 
 variable (X) in
@@ -176,7 +176,7 @@
     {x : X} {r : ℝ} {ϕ : X → ℂ} (h2 : tsupport ϕ ⊆ ball x r) {f g : Θ X} :
     ‖∫ x, exp (I * (f x - g x)) * ϕ x‖ₑ ≤
     (A : ℝ≥0∞) * volume (ball x r) * iLipENorm ϕ x r * (1 + nndist_{x, r} f g) ^ (- τ) := by
-  rcases le_or_lt r 0 with hr | hr
+  rcases le_or_gt r 0 with hr | hr
   · simp only [ball_eq_empty.2 hr, subset_empty_iff, tsupport_eq_empty_iff] at h2
     simp [h2]
   rcases eq_or_ne A 0 with rfl | hA
@@ -205,7 +205,7 @@
     congr 1
     rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)]
     have : ϕ y = 0 := by
-      apply nmem_support.1
+      apply notMem_support.1
       contrapose! hy
       exact (subset_tsupport _).trans h2 hy
     simp [this]
@@ -213,7 +213,7 @@
       ENNReal.ofReal_mul (by positivity)]
     congr
     · simp
-    · simp only [Measure.real, ofReal_toReal (measure_ball_ne_top _ _)]
+    · simp only [Measure.real, ofReal_toReal (carleson_measure_ball_ne_top _ _)]
     · simp [iLipNNNorm, coe_toNNReal h1]
     · rw [← ENNReal.ofReal_rpow_of_pos (by positivity)]
       congr
@@ -236,7 +236,7 @@
   [IsFiniteMeasureOnCompacts (volume : Measure X)] {x y : X} :
     ENNReal.ofReal (Real.vol x y) = vol x y := by
   simp_rw [Real.vol_def, ENNReal.ofReal_toReal_eq_iff, vol]
-  apply measure_ball_ne_top
+  apply carleson_measure_ball_ne_top
 
 -- /-- In Mathlib we only have the operator norm for continuous linear maps,
 -- and `T_*` is not linear.
@@ -446,9 +446,9 @@
   | succ k ih =>
     trans 2 * dist_{x, (defaultA a) ^ k * r} f g
     · rw [pow_succ', mul_assoc]
-      exact (_root_.mul_le_mul_left zero_lt_two).mpr ih
+      exact (by gcongr)
     · convert le_cdist (ball_subset_ball _) using 1
-      · exact dist_congr rfl (by rw [← mul_assoc, pow_succ'])
+      · exact legacy297_dist_congr rfl (by rw [← mul_assoc, pow_succ'])
       · nth_rw 1 [← one_mul ((defaultA a) ^ k * r)]; gcongr
         rw [← Nat.cast_one, Nat.cast_le]; exact Nat.one_le_two_pow
 
@@ -459,9 +459,9 @@
   | succ k ih =>
     trans defaultA a * dist_{x, 2 ^ k * r} f g
     · convert cdist_le _ using 1
-      · exact dist_congr rfl (by ring)
+      · exact legacy297_dist_congr rfl (by ring)
       · rw [dist_self]; positivity
-    · replace ih := (mul_le_mul_left (show 0 < (defaultA a : ℝ) by positivity)).mpr ih
+    · have ih : (defaultA a : ℝ) * dist_{x, 2 ^ k * r} f g ≤ (defaultA a : ℝ) * ((defaultA a : ℝ) ^ k * dist_{x, r} f g) := mul_le_mul_of_nonneg_left ih (by positivity)
       rwa [← mul_assoc, ← pow_succ'] at ih
 
 lemma ballsCoverBalls_iterate_nat {x : X} {d r : ℝ} {n : ℕ} :
@@ -771,7 +771,7 @@
     have : z ≠ z' → Disjoint (g z) (g z') := g_pd hz hz'
     rw [← e, Finset.disjoint_self_iff_empty] at this
     exact not_ne_iff.mp <| this.mt <| Finset.nonempty_iff_ne_empty.mp (g_ne z hz)
-  have g_subset : g '' 𝓩 ⊆ 𝓩'.powerset.toSet := fun gz hgz ↦ by
+  have g_subset : g '' 𝓩 ⊆ (𝓩'.powerset : Set _) := fun gz hgz ↦ by
     rw [mem_image] at hgz
     obtain ⟨z, hz⟩ := hgz
     simp_rw [Finset.coe_powerset, mem_preimage, mem_powerset_iff, Finset.coe_subset, ← hz.2, g,
@@ -850,7 +850,7 @@
   by_cases hx : x ∈ ball z R
   · apply norm_le_iLipNNNorm_of_mem hϕ hx
   · have : x ∉ support ϕ := fun a ↦ hx (h a)
-    simp [nmem_support.mp this]
+    simp [notMem_support.mp this]
 
 lemma LipschitzOnWith.of_iLipENorm_ne_top
     {z : X} {R : ℝ} {ϕ : X → ℂ} (hϕ : iLipENorm ϕ z R ≠ ⊤) :
@@ -902,7 +902,7 @@
   by_cases hx : x ∈ ball z R
   · apply norm_le_iHolNNNorm_of_mem hϕ hx
   · have : x ∉ support ϕ := fun a ↦ hx (h a)
-    simp [nmem_support.mp this]
+    simp [notMem_support.mp this]
 
 lemma HolderOnWith.of_iHolENorm_ne_top
     {z : X} {R : ℝ} {ϕ : X → ℂ} (hϕ : iHolENorm ϕ z R ≠ ⊤) :
@@ -943,7 +943,7 @@
 lemma continuous_of_iHolENorm_ne_top' {z : X} {R : ℝ}
     {ϕ : X → ℂ} (hϕ : support ϕ ⊆ ball z R) (h'ϕ : iHolENorm ϕ z (2 * R) ≠ ∞) :
     Continuous ϕ := by
-  rcases le_or_lt R 0 with hR | hR
+  rcases le_or_gt R 0 with hR | hR
   · have : support ϕ ⊆ ∅ := by rwa [ball_eq_empty.2 hR] at hϕ
     simp only [subset_empty_iff, support_eq_empty_iff] at this
     simp only [this]
```
