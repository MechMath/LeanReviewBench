# Registered project data format

This is the repository's preparation/merge format. It is not a frozen scoring export. A retained input is one project snapshot; a multi-root snapshot remains one input and one label record. Related versions share group/split identities and reciprocal version links. Root counts and input counts must be reported separately.

## Authoritative files

| File | Contract |
| --- | --- |
| `datasets/project-cases.json` | Registered batches and pinned Lean/Mathlib/Cslib environment; directories outside this inventory are not evaluation inputs |
| `datasets/<batch>/projects/<id>/project.json` | `paperlean-project-case-1`: source repository, full commit, targets, informal IDs, version/group links, formal inventory, input digest and independent technical/label states |
| `informal.jsonl` | One JSON object per line: ID, independently sourced text, source version/locator/hash, scope and selected target declaration(s). Empty inputs must be disclosed; never synthesize a target from Lean |
| `formal/Main.lean`, `formal/dep/` | Selected source plus repository-local import closure and required runtime resources; external libraries remain pinned boundaries |
| `technical/`, `graph/`, `context/` and receipt locators | Compilation logs, actual exporter results and source bindings. Consult the package's metadata/receipt path rather than assuming every historical batch uses the same graph directory |
| `datasets/<batch>/index.csv` | Generated from project metadata. Exact columns: `id,root,commit,group_id,before_ids,after_ids,status`. The root column joins all selected declaration names with semicolons; authoritative root metadata remains in `targets` |
| `metadata/labels/<batch>.jsonl` | One input-bound label record per registered project: dataset, project ID, root, `aligned`/`misaligned` label, concise English reason and scope, input hash, and current human-review state. `undetermined` is accepted by legacy validation but none remains in the audited latest research snapshot |
| `metadata/evidence/analysis/<batch>/<id>.json` | Input-bound judgment evidence and available detailed reasoning, hashed by the analysis index. The outer `roots` array covers every selected target; coverage status distinguishes detailed reviews, reason-only records, and missing reasons |
| `metadata/provenance.json`, `metadata/manifest.json`, `licenses/index.json` | Project provenance, current byte inventory and source-license attribution. Regenerate after accepted metadata changes |

Project `status` is historical workflow metadata: `ready` commonly corresponds to an aligned label, but an aligned input can remain technically `blocked`. Use the label file for semantic labels, and compilation/extraction flags plus receipts for technical availability. Before does not imply misaligned; after does not imply aligned.

## Review states and model-visible boundary

All 171 current labels record `human_adjudicated=true` and
`review_status=human_reviewed`. Their reasons and review scopes are concise
English annotations. Process fields, dialogue excerpts, previous states, and
per-record evidence paths/hashes are excluded from labels. Evidence associations
are indexed in `metadata/evidence/analysis/index.json`. Formal export readiness
remains separate: `reference_ready=false` and `gold_label=null` are unchanged.

A task loader must construct the mathematical input from the selected informal target, formal roots and dependency context. Keep label reasons, review reports, before/after repair clues and reference metadata outside model-visible input. Do not copy the whole project metadata tree into a scoring prompt. Model output is `aligned` or `misaligned`; a negative decision requires a mathematical reason and declaration evidence.

Existing legacy eligibility fields are not sufficient to establish reference readiness: the audited repository has six legacy inputs with `evaluation_eligible=true`, but zero `reference_ready=true`. A scoring release must require a deliberate reference-readiness decision and appropriate technical/material checks.

## Verification

```sh
python3 scripts/data/project_cases.py check
python3 scripts/data/annotation_coverage.py
python3 scripts/data/check_release_candidate.py
python3 -m unittest discover -s tests -p 'test_*.py'
```

The coverage audit checks exact input/label bindings, binary coverage, root scope and current hashed review reports. Historical archive report locators without current report hashes are not treated as local missing files. Three legacy sphere-packing aligned records have empty reasons; the audit reports these as warnings without inventing justifications.

Compilation success is not proof completeness or semantic approval. The two retained KZG function-binding inputs still have only dated cached paper text; the exact original PDF revision/hash is unverified. Preserve that qualification in any merge or release.

## Refactor integration compatibility

Explicit `target_mode: joint` packages retain refactor’s hash over the full targets and target mode, and must bind one shared joint informal record and the complete roots in their label. Previously reviewed research multi-root packages without that marker retain their established root-plus-roots hash. Both include non-Lean runtime resources when present. The integration must not silently change the digest scheme of an already labeled input.

## Publication directory consolidation

The release groups upstream statements under `metadata/evidence/upstream/` and
our current judgment evidence under `metadata/evidence/analysis/<batch>/<id>.json`.
The analysis index binds input identities and hashes to analysis paths and SHA-256. Graph receipts and
composition inputs live under `metadata/derived-graphs/`; exact aliases in
`metadata/layout.json` resolve embedded retained historical locators. Active
indexes use canonical paths. Verdicts, root bindings and input digests are unchanged. Reasons and scope are
normalized to concise English, human-review status is explicit, and evidence
index hashes are refreshed.
Python tools remain under `scripts/`; the evaluation contract is
`scripts/evaluation/PROTOCOL.md`.
