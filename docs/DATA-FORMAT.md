# Registered project data format

The native dataset schema is `paperlean-project-case-1`. It is not a frozen scoring export. A retained input is one project snapshot; a multi-root snapshot remains one input and one label record. Related versions share group/split identities and reciprocal version links. Root counts and input counts must be reported separately.

Datasets awaiting human review use the same `datasets/<batch>/projects/` layout.
They are listed in `review_datasets` in the registry; `datasets` lists the
human-reviewed release batches. Both use the authoritative native label,
analysis, validation and provenance paths below. Per-batch `metadata/` retains
only deferred development plans and archive locators. Unresolved judgments are
`undetermined` with `human_adjudicated=false`; they are not assigned binary labels.
Excluded or technically deferred contexts are absent from publication datasets;
the plans retain their source pins and preparation revision.

The qinz1yang and FrenzyMath batches remain separate sources with separate
informal bindings. All 26 retained contexts meet the same native format and
recorded context-check requirements as the original 171 inputs. Compact technical
evidence is in `metadata/evidence/technical/`, without local build dependencies.
Human review and source-admission decisions are separate metadata states. A
source-specific curator decision may admit an unresolved historical license
evidence association with a notice, without claiming an established grant.

## Authoritative files

| File | Contract |
| --- | --- |
| `datasets/project-cases.json` | Registered batches and pinned Lean/Mathlib/Cslib environment; directories outside this inventory are not evaluation inputs |
| `datasets/<batch>/projects/<id>/project.json` | `paperlean-project-case-1`: source repository, full commit, targets, informal IDs, version/group links, formal inventory, input digest and independent technical/label states |
| `informal.jsonl` | One JSON object per line: ID, independently sourced text, source version/locator/hash, scope and selected target declaration(s). Empty inputs must be disclosed; never synthesize a target from Lean |
| `formal/Main.lean`, `formal/dep/` | Statement-only declaration closure, necessary source elaboration support and runtime resources; external libraries remain pinned boundaries |
| `CHANGES.md` | Concise per-input Lean migration changes and statement-context packaging notes |
| `metadata/validation.json` | Input-bound results of context compilation, extraction and preservation checks; no graph data |
| `datasets/<batch>/index.csv` | Generated from project metadata. Exact columns: `id,root,commit,group_id,before_ids,after_ids,status`. The root column joins all selected declaration names with semicolons; authoritative root metadata remains in `targets` |
| `metadata/labels/<batch>.jsonl` | One input-bound label record per registered project: dataset, project ID, root, `aligned`/`misaligned` label, concise English reason and scope, input hash, and current human-review state. `undetermined` is permitted for pending records, with an explicit non-human-reviewed state |
| `metadata/evidence/analysis/<batch>/<id>.json` | Input-bound judgment evidence and available detailed reasoning, hashed by the analysis index. The outer `roots` array covers every selected target; coverage status distinguishes detailed reviews, reason-only records, and missing reasons |
| `metadata/provenance.json`, `metadata/manifest.json`, `licenses/index.json` | Project provenance, current byte inventory and source-license attribution. Regenerate after accepted metadata changes |

Project `status` is historical workflow metadata: `ready` commonly corresponds to an aligned label, but an aligned input can remain technically `blocked`. Use the label file for semantic labels, and compilation/extraction flags plus receipts for technical availability. Before does not imply misaligned; after does not imply aligned.

## Review states and model-visible boundary

The original 171 labels record `human_adjudicated=true` and
`review_status=human_reviewed`. All 26 added records have also been confirmed
by the user, including sixteen accepted in a batch, and have the same human-review
state. Explicit user verdicts that differ from the agent assessment are disclosed
in the reason and analysis evidence; human review does not certify a Lean proof. Individual verdicts are authoritative in the label records. Their
reasons and review scopes are concise English annotations. Process fields,
dialogue excerpts, previous states, and per-record evidence paths/hashes are
excluded from labels. Evidence associations are indexed in
`metadata/evidence/analysis/index.json`. Formal export readiness remains
separate: `reference_ready=false` and `gold_label=null` are unchanged.

A task loader must construct the mathematical input from the selected informal target, formal roots and dependency context. Keep label reasons, review reports, before/after repair clues and reference metadata outside model-visible input. Do not copy the whole project metadata tree into a scoring prompt. Model output is `aligned` or `misaligned`; a negative decision requires a mathematical reason and declaration evidence.

Existing legacy eligibility fields are not sufficient to establish reference readiness: the audited repository has six legacy inputs with `evaluation_eligible=true`, but zero `reference_ready=true`. A scoring release must require a deliberate reference-readiness decision and appropriate technical/material checks.

## Refactor integration compatibility

Explicit `target_mode: joint` packages retain refactor’s hash over the full targets and target mode, and must bind one shared joint informal record and the complete roots in their label. Previously reviewed research multi-root packages without that marker retain their established root-plus-roots hash. Both include non-Lean runtime resources when present. The integration must not silently change the digest scheme of an already labeled input.

## Release layout

```text
datasets/              Registered formal/informal packages and batch indexes
metadata/              Labels, evidence, taxonomy, graphs and integrity inventories
scripts/data/          Dataset inspection and native validation
scripts/construction/  Optional Lean compilation and tool resolution
scripts/evaluation/    Existing task protocol, runner, adapters and scorer
scripts/maintenance/   Release maintenance and integrity tools
docs/                  Current documentation
tests/                 Offline regression tests
licenses/              Source attribution and license copies
```

`metadata/validation.json` records successful compilation, extraction and statement/
non-proof-definition preservation checks for all 197 retained inputs. Each record
is bound to its input digest, formal-source digest and ordered roots; shared Lean,
Mathlib/Cslib pins and exporter hashes are recorded once. It explicitly records
proof erasure without certification of original proofs. Offline validation checks
these bindings and coverage; it does not rerun Lean. The evidence commit identifies
the Git revision containing the original detailed receipts.

The Lean files under each input's `formal/` directory are authoritative. Dependency
graphs are generated on demand into ignored build directories. Graphs, historical
graph variants and composition inputs are not distributed. Raw generated graphs
may contain documentation and require filtering before model use.

`metadata/evidence/analysis/index.json` associates each input with its current analysis file and hash. `metadata/layout.json` resolves historical paths for retained semantic judgment evidence. Removed technical artifacts remain accessible in Git history. The taxonomy standard and classification records are documented in [metadata/taxonomy](../metadata/taxonomy/README.md).

`metadata/manifest.json` inventories data, metadata and license bytes. `metadata/support-inventory.json` inventories current documentation, configuration, scripts and tests. Source attribution and archive locators are recorded in `metadata/provenance.json`, `metadata/materials/index.json` and `metadata/release.json`.

## Technical states and limits

All 197 retained statement contexts have recorded Lean 4.34.1 compilation and fresh dependency extraction. The added 26 records explicitly retain the limitation that original-toolchain elaboration was not checked. Each `formal` inventory records `declaration_slice=true` and `proofs_erased=true`. The retained declarations preserve root types and necessary computational definitions; theorem/lemma proofs and proof-valued declaration bodies are replaced by `sorry`. Proof-valued tactic blocks inside data definitions are erased while computational tactic blocks remain. Source-level notation, aliases, instances and compiler support may be required in addition to the mathematical graph closure. Compilation of these contexts does not establish proof completeness or semantic alignment.

Three sphere-packing aligned records have empty reasons; the coverage audit reports them without inventing justifications. Two KZG function-binding inputs lack a verified exact original PDF revision/hash. The AppliedModelingLib historical license-copy gap is recorded in `licenses/index.json`.

The release excludes `YuanheZ/lean-stat-learning-theory` and its sole input `slt-master`: statement-only context recovery did not resolve its full historical migration. This does not exclude the separate FormalSLT batch. Registered scope and exclusions are defined by `datasets/project-cases.json` and `metadata/release.json`.

## Packaging and evaluation boundary

The release retains registered source/resource files, complete informal records, compatibility notes, labels, evidence, graph bindings and source licenses. Build caches, experiment outputs, excluded candidates, duplicate source archives, optional acquisition caches and historical production logs are omitted. Independent mathematical text remains in `informal.jsonl`; optional acquired materials have pinned archive locators and hashes in `metadata/materials/index.json`.

Native packages contain proof-erased declaration contexts, source comments and curator metadata. They still require a deliberate model-input export. Existing [evaluation tools](../scripts/evaluation/PROTOCOL.md) construct `input.json` from separately supplied evaluation JSONL packages; they do not currently convert native inputs or generate native dependency graphs automatically. Model input scope and native conversion are tracked in [issue #1](https://github.com/MechMath/LeanReviewBench/issues/1).

The active source snapshot is pinned in `metadata/release.json`. Historical research documentation can be consulted at the [recorded documentation revision](https://github.com/MechMath/PaperLeanBench/tree/2f471585a4b71adb32f6e3fac214e366ce8979ae/docs); it does not override the current release contract.
