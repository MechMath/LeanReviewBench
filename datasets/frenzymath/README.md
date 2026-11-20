# frenzymath

11 complete Lean 4.34.1 statement contexts use the native
`paperlean-project-case-1` layout. All 11 judgments are human confirmed
(three aligned and eight misaligned), including six accepted by explicit user
batch confirmation. FM-COVERING-before records an explicit user misaligned
verdict after source-text correction. Its final written reason identifies the
positive-dimension hypothesis, which omits the zero-dimensional cases allowed by
the bound target; the old disconnected-source objection remains withdrawn.
Review state is separate from reference readiness.
The source repositories and informal sources remain separate between batches.

- [Native index](index.csv); sources, targets, version links and review states
  are recorded in each `projects/<id>/project.json`.
- Labels: `metadata/labels/frenzymath.jsonl` at the repository root.
- Analysis: `metadata/evidence/analysis/frenzymath/` at the repository root.
- Compilation, extraction and migrated preservation: root `metadata/validation.json`;
  compact input-bound evidence: `metadata/evidence/technical/frenzymath/`.
- Source provenance: root `metadata/provenance.json`; exact license/notice
  associations: root `licenses/index.json`.
- [Deferred development plan](metadata/deferred-development-plan.jsonl) and
  [archived preparation locators](metadata/archive.json).

Original-toolchain elaboration is not certified. Migrated expression comparisons
retain their documented nominal-identity and exact-source-reuse qualifications.
No original theorem proof or human alignment verdict is certified by compilation.

Deferred or excluded contexts are absent from this dataset. Full graphs, source
acquisition caches and trial contexts are available only through the archived
preparation revision, not as dependencies of normal validation.

Run from the repository root:

```sh
python3 scripts/data/check_release_candidate.py
python3 scripts/data/publication_readiness.py
# Strict gate: requires human binary judgments and documented admission states.
python3 scripts/data/check_release_candidate.py --require-reviewed
```

All 11 versions have the same pinned Apache-2.0 license copy. The geodesic-completeness pair has identical input content and one shared split/group: retain the historical revisions, but count once for independent errors or evaluation contexts.
