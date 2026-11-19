# qinz1yang/differential-geometry

9 families, 18 retained historical snapshots; 15 declaration slices and 3 partial support contexts.

These inputs await human review. Their directory is the normal dataset layout;
review, exclusion and technical states are recorded in JSON. They are listed in
`review_datasets` in the shared registry. None is a human-adjudicated or gold input.
Original-toolchain elaboration remains unchecked; recorded preservation concerns
migrated statement contexts and computational definitions, not original proofs.
Historical source-license qualifications remain explicit in project metadata.

- [Index](index.json) and [version links](metadata/version-pairs.json).
- [Current review snapshot](metadata/current-review-snapshot.json).
- [Prior six-family batch audit](metadata/prior-batch-audit.json).
- [Latest retained-family processing](metadata/retained-processing.json).
- [Deferred development plan](metadata/deferred-development-plan.jsonl).
- [Screening summary](metadata/screening/screening-summary.json).
- [Technical validation](metadata/technical-validation.json) and compact receipts
  under `metadata/technical-evidence/`.

Provisional binary judgments are in `metadata/provisional-labels.jsonl`; unresolved
scope judgments are in `metadata/pending-scope-reviews.json`. Keep these and repair
clues outside model-visible inputs. Before/after does not determine the label.
Related snapshots share their source split group. FrenzyMath's geodesic-completeness
pair has identical mathematical inputs at two revisions and must be deduplicated
before evaluation.

Full graphs, compiler logs and independent acquired PDFs remain optional local
build artifacts. Persistent receipts retain their original hashes and locators.
A default check verifies committed inputs and receipts; it does not rerun Lean or
require those build artifacts.

```sh
python3 scripts/construction/review_batches/check_batch.py --batch qinz1yang
# Optional: also check locally retained extraction graphs.
python3 scripts/construction/review_batches/check_batch.py --batch qinz1yang --with-build-graphs
```

[Technical follow-up](metadata/retained-technical-followup.jsonl) records the rejected convergence proof-erasure attempt. It is a preparation-tool failure, not an upstream error. Both convergence versions remain partial support contexts; the separate late-slice convergence root was not packaged. Sobolev-after also retains a wider support closure.
