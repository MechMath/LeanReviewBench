# qinz1yang

15 complete Lean 4.34.1 statement contexts use the native
`paperlean-project-case-1` layout. Their binary alignment judgments await human
review; provisional judgments do not imply approval or reference readiness.
The source repositories and informal sources remain separate between batches.

- [Native index](index.csv); sources, targets, version links and review states
  are recorded in each `projects/<id>/project.json`.
- Labels: `metadata/labels/qinz1yang.jsonl` at the repository root.
- Analysis: `metadata/evidence/analysis/qinz1yang/` at the repository root.
- Compilation, extraction and migrated preservation: root `metadata/validation.json`;
  compact input-bound evidence: `metadata/evidence/technical/qinz1yang/`.
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
# Strict gate: requires completed human binary judgments AND resolved licenses.
python3 scripts/data/check_release_candidate.py --require-reviewed
```

Of these 15 versions, 4 have pinned Apache-2.0 license/notice copies; 11 have unresolved historical licensing scope. Human labels alone do not clear that merge blocker.
