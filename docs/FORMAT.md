# Release format, version 1

The source project format, release package format and prediction protocol are distinct. This release does not copy the older three-verdict protocol: predictions are binary.

## Git and data layout

```text
leanreviewbench/       # Loader, inventory verifier, scorer, CLI
releases/<version>/
  manifest.json       # Per-directory file sizes and SHA-256 hashes
  catalog.csv         # Evaluator-only mapping; never a model prompt resource
licenses/             # Original attribution copies and provenance index
data/<version>/       # Uncompressed files, tracked by Git for the preview
  inputs/
    tasks.jsonl
    contexts/<sha256>.json
  references/
    labels.jsonl
    provenance.jsonl
    reviews/<task-id>.json
  reproduction/
    projects.jsonl
    environment.json
    blobs/<sha256>
    evidence/<task-id>/...
```

The manifest is `leanreviewbench-release-2`; its source repository/commit fixes the research origin. Its `directories` array lists the `inputs`, `references` and `reproduction` roles. Each entry has a relative directory `path`, total byte `size`, and a `files` inventory with relative `path`, byte `size` and `sha256`. There are no archive URLs or compressed-package dependencies. `validate --manifest` verifies every tracked data file against this inventory and rejects missing, unexpected or changed files and symlinks. Hashes provide byte integrity, not a digital signature.

## Mathematical input

A `leanreviewbench-input-1` row has exactly `schema_version`, opaque `task_id`, ordered `roots`, `informal`, `context_id`, `environment`. Informal records expose only the selected independent `id` and `text`. Original bibliographic, editorial scope, review and label metadata stays in evaluator provenance; no new mathematical qualification is synthesized. When qualifications appear in the independent text, they remain visible verbatim. The release does not independently adjudicate whether every source contains sufficient qualifications.

The context ID is the SHA-256 of canonical UTF-8 JSON (sorted keys, compact separators, final newline). A `leanreviewbench-context-1` contains selected roots, declarations, dependency edges and explicit external-boundary policy. Nodes expose Lean names, kinds, actual types/non-proof values, external/proof flags and structural metadata. Docstrings, module source paths, line ranges, reviewer commentary and labels are removed by an allowlist. Exported type/value strings are preserved without re-elaboration or shortening. Theorems and other proof-valued nodes never expose values or value-dependency traversal. Edge sites are `type`, `definition_value` and `constructor_type`.

`Dataset.task()` expands a graph reference into `leanreviewbench-task-1`: `schema_version`, `task_id`, `roots`, `informal`, `formal_context`, `environment`. This is the model-visible contract. It never reads `references/` or `reproduction/`. The reproduction directory contains proofs/comments and review evidence and must not be mounted as a model task resource. Identifier and source-text clues inherent in the mathematics are not claimed to be anonymized.

Multi-root inputs remain one task. Version pairs retain separate input identities. Do not split train/test sets by snapshots independently: use evaluator provenance `split_group`/`group_id` to avoid related-version leakage. No arbitrary official split is introduced by this migration.

## Labels and provenance

Each reference row binds a task ID and canonical payload hash to a binary label. It also preserves the original research input digest and the complete original label record, including the exact review/adjudication flags and original evidence locators. Current hashed review reports are bundled where retained; some historical review paths remain archive provenance locators, not runtime file dependencies.

Provenance preserves the original project identity, commit/source, input hash, selected graph's exact source commit/path/hash, version relationships, grouping, compilation flag, independent source records and material caveats. It is evaluator-only. A migrated context can come from a verified recovered statement graph even if the original complete source package could not compile; these facts are kept separate.

The normalization creates a new payload hash; it does not overwrite or reinterpret any original input hash or label. The manifest and source inventory cover byte integrity. They do not assert semantic equivalence merely from hashing.

## Optional reproduction

`projects.jsonl` maps each task to exact original project metadata, informal records and a map of formal paths to content digests. `blobs/` deduplicates identical Lean/resource files and acquired source material. `restore` checks every digest and recreates the formal snapshot in a fresh directory. No `.olean`, build cache, copied external Mathlib or credentials are distributed. Compatible compiler environments remain separately pinned in `environment.json`.

## Reference readiness

All 172 labels are provisional, with zero reference-ready records. Development scoring requires `--allow-provisional`. No field is promoted during migration. Missing legacy justification and incomplete original PDF-version provenance remain visible in the original records. A final gold/scoring release requires a separate, deliberate decision.
