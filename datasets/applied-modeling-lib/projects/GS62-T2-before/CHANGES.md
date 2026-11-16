# Changes from the selected upstream snapshot

These changes prepare historical Formal for Lean 4.34.1. Upstream before/after fixes are separate snapshots; the compatibility port does not replace the selected historical revision.

Packaging additionally relocates the target module to `formal/Main.lean`, places retained local imports under `formal/dep/`, and rewrites only local import paths. Namespaces, declaration names, binders, definition values and proof source are retained.

The following exact diffs retain the recorded compatibility choices. Source hash and import-relocation checks do not prove global equivalence of the historical and modern library environments.

## EconCSLib/Markets/Matching/ManyToOne.lean

```diff
--- upstream/EconCSLib/Markets/Matching/ManyToOne.lean
+++ lean-4.34.1/EconCSLib/Markets/Matching/ManyToOne.lean
@@ -311,7 +311,8 @@
   rcases hstable with ⟨happIR, hcollegeIR, hnoBlock⟩
   refine ⟨ManyToOneAssignment.ofOneToOne_respects_quota_one mu, ?_, ?_, ?_⟩
   · intro a
-    simpa [valApplicant, ManyToOneAssignment.ofOneToOne, valM] using happIR a
+    cases hmatch : mu.m_match a <;>
+      simpa [valApplicant, ManyToOneAssignment.ofOneToOne, valM, hmatch] using happIR a
   · intro c a ha
     have ha_match : mu.m_match a = some c :=
       (ManyToOneAssignment.mem_college_roster_ofOneToOne_iff mu a c).1 ha
@@ -319,7 +320,8 @@
     simpa [valW, hc_match] using hcollegeIR c
   · intro a c happPref hcollegeAccept
     have happPref' : valM val_applicant a (mu.m_match a) < val_applicant a c := by
-      simpa [valApplicant, ManyToOneAssignment.ofOneToOne, valM] using happPref
+      cases hmatch : mu.m_match a <;>
+        simpa [valApplicant, ManyToOneAssignment.ofOneToOne, valM, hmatch] using happPref
     have hcollegePref :
         valW val_college c (mu.w_match c) < val_college c a := by
       rcases hcollegeAccept with ⟨hpos, hroom⟩ | ⟨a', ha', hpref⟩
```
