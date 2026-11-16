# Publication layout

The active collection contains 172 project-case inputs across 17 registered batches. The [native format](DATA-FORMAT.md) and [packaging policy](PACKAGING.md) define what is included.

```text
datasets/         Registered packages, exact formal resources and informal records
metadata/         Labels, graphs, source provenance and integrity inventories
reports/          Only evidence files consumed by label/graph validation
protocol/         Versioned schemas, adapter contracts and setup templates
scripts/data/     Native data checks, statistics and provenance lookup
scripts/construction/  Optional compiler and dependency resolution
scripts/evaluation/    Export/runner/scorer for supplied evaluation packages
docs/             Current guides and pinned contract documentation
tests/            Offline regression and publication checks
tools/            Release migration and support-file verification
```

Source code and mathematical inputs are uncompressed and Git-tracked. Generated exports, runs, Lean caches, build output, local environments and credentials remain ignored. Historical raw source copies, optional paper caches, unsuccessful candidates and production logs are not needed to test the publication and are not bundled.

The new release repository has no imported research Git history. Earlier local preview commits remain local history; this cleanup does not rewrite them. Historical provenance is pinned to the source commits recorded in `metadata/release.json`.
