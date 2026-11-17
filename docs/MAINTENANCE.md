# Dataset maintenance

Use the [data format](DATA-FORMAT.md) to distinguish mathematical inputs, semantic labels, technical evidence and model-export readiness. Generated inventories detect changes; refreshing them does not approve a semantic change.

## Updating records

1. For a new or changed input, record the upstream repository/revision, independently sourced informal text and qualifications, selected root(s), compatibility edits, and complete local formal/resource inventory. Follow the [construction method](CONSTRUCTION.md).
2. Update the native input digest and all affected root/input bindings deliberately. Preserve the established digest scheme for existing multi-root inputs. Maintain reciprocal version links and shared split groups; before/after order does not determine alignment.
3. Review affected binary labels and their concise English reasons/scopes. Keep current results in `metadata/labels/`; update input-bound evidence and its index under `metadata/evidence/analysis/`. Preserve explicit upstream claims separately. Update affected taxonomy records, evidence hashes and summary hashes according to [the taxonomy documentation](../metadata/taxonomy/README.md).
4. Update affected graph indexes and receipt bindings, provenance, source material locators, license records and `metadata/release.json` counts. Keep historical technical states distinct from current semantic judgments. Input edits can invalidate prior extraction or review evidence.
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

The active source and documentation revisions are recorded in `metadata/release.json`. Historical `reports/...` provenance can be resolved with `scripts/data/provenance.py --path <original-path>`. Current embedded technical path aliases are handled by `metadata/layout.json`.

The optional archive reconstruction helper requires a clean pinned research checkout and its local archive Git objects:

```sh
python3 scripts/maintenance/migrate.py --source /path/to/clean/research-checkout \
  --output /path/to/fresh-publication-directory
```

It reconstructs source packages and carries the curated current release metadata and support files, including deliberate exclusions. It is separate from a fresh Lean build or source-to-model task export. Ordinary data use and validation do not require this reconstruction.
