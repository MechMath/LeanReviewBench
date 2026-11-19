# Dataset maintenance

Use the [data format](DATA-FORMAT.md) to distinguish mathematical inputs, semantic labels, technical evidence and model-export readiness. Generated inventories detect changes; refreshing them does not approve a semantic change.

## Updating records

1. For a new or changed input, record the upstream repository/revision, independently sourced informal text and qualifications, selected root(s), compatibility edits, and complete local formal/resource inventory. Follow the [construction method](CONSTRUCTION.md).
2. Update the native input digest and all affected root/input bindings deliberately. Preserve the established digest scheme for existing multi-root inputs. Maintain reciprocal version links and shared split groups; before/after order does not determine alignment.
3. Review affected binary labels and their concise English reasons/scopes. Keep current results in `metadata/labels/`; update input-bound evidence and its index under `metadata/evidence/analysis/`. Preserve explicit upstream claims separately. Update affected taxonomy records, evidence hashes and summary hashes according to [the taxonomy documentation](../metadata/taxonomy/README.md).
4. Update affected records in `metadata/validation.json` after recompilation, extraction and preservation checks, along with provenance, source material locators, license records and `metadata/release.json` counts. Keep historical technical states distinct from current semantic judgments. Input edits invalidate prior context-check bindings and may invalidate review evidence. Keep generated graphs in ignored build directories.
5. Regenerate batch indexes and statistics, refresh integrity inventories, and run the checks below. Generated outputs and temporary review material belong under ignored `build/` directories.

## Generated files and checks

```sh
python3 scripts/data/project_cases.py index
python3 scripts/data/project_case_stats.py > docs/STATISTICS.md
python3 scripts/maintenance/check_support_files.py --freeze
python3 scripts/data/release_metadata.py freeze
python3 scripts/data/check_release_candidate.py
python3 scripts/data/annotation_coverage.py
python3 scripts/data/inspect_dataset.py validate
python3 -m unittest discover -s tests -v
```

Refresh `metadata/support-inventory.json` before `metadata/manifest.json`, because the manifest includes the support inventory. The support inventory covers current documentation, configuration, tools and tests; the manifest covers native data, metadata and licenses. Consult [validation](VALIDATION.md) for what each check establishes. Read-only checks do not need Lean, credentials, network access or a research checkout.

Changes to model-visible content require explicit task and reference bindings under the eventual evaluation protocol. Existing evaluation tools accept separately supplied packages; native conversion and model input scope are tracked in [issue #1](https://github.com/MechMath/LeanReviewBench/issues/1).

## Archive reconstruction

The active source and documentation revisions are recorded in `metadata/release.json`. Historical `reports/...` provenance can be resolved with `scripts/data/provenance.py --path <original-path>`. Retained semantic evidence aliases are handled by `metadata/layout.json`; removed technical artifacts remain in Git history.

The maintained artifacts are the released statement-only Lean contexts and each input's `CHANGES.md`. Full original projects can be located by repository/commit/root pins. Executable migration histories and complete upstream source archives are not required for benchmark use. Obsolete archive-restoration tools and their graph dependencies are omitted.

## Completing the new source-batch reviews

Annotate `metadata/labels/qinz1yang.jsonl` and `metadata/labels/frenzymath.jsonl`
using the same binary label/reason/scope contract as existing batches. A completed
record has `human_adjudicated=true` and `review_status=human_reviewed`; unresolved
rows stay preliminary. Keep the matching analysis verdicts, project statuses,
provenance hashes and inventories synchronized using the update steps above.
Do not change formal source or independent mathematical text merely to accept a
label. Source-license claims must have independently retained evidence. A curator
may explicitly admit a specific evidence gap with a documented notice; that
decision must not be recorded as a license grant or as resolved historical scope.

Run the native checks and `check_release_candidate.py --require-reviewed` before
merge. The gate checks native schema and hashes, complete technical contexts,
human binary judgments and documented license/admission states. It does not promote
`reference_ready` or `gold_label`, nor require restoring trial build directories.
