# Publication layout

The active collection contains 172 project-case inputs across 17 registered batches. The [native format](DATA-FORMAT.md) and [packaging policy](PACKAGING.md) define what is included.

```text
datasets/              Registered packages and exact formal/informal resources
metadata/              Labels, graphs, reports, provenance and integrity inventories
scripts/data/          Dataset loading, inspection and native validation
scripts/construction/  Optional Lean compiler and dependency resolution
scripts/evaluation/    Protocol docs/schema, exporter, runner, scorer and adapter
scripts/maintenance/   Migration, byte comparison and support-file verification
docs/                  Current guides and pinned source contracts
tests/                 Offline regression and publication checks
licenses/              Upstream license copies and attribution
```

Source code and mathematical inputs are uncompressed and Git-tracked. Generated exports, runs, Lean caches, build output, local environments and credentials remain ignored. Historical raw source copies, optional paper caches, unsuccessful candidates and production logs are not needed to test the publication and are not bundled.

The new release repository has no imported research Git history. Earlier local preview commits remain local history; this cleanup does not rewrite them. Historical provenance is pinned to the source commits recorded in `metadata/release.json`.

The former top-level `leanreviewbench/`, `references/`, `reports/`, `protocol/` and `tools/` directories have been consolidated. Python code lives in `scripts/`; evidence lives in `metadata/`. `metadata/layout.json` records the `reports/` prefix alias, preserving old hash-bound references without rewriting labels or receipts. The only provider template is `scripts/evaluation/.env.example`.
