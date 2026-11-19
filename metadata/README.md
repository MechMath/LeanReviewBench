# Benchmark metadata

The release contains 171 versioned inputs across 16 batches, with 81 aligned and
90 misaligned human-reviewed labels. Metadata are curator-facing and must remain
outside model-visible task exports.

| Path | Purpose |
| --- | --- |
| `labels/` | Human-reviewed binary verdicts, concise English reasons, scope, and input bindings |
| [evidence/upstream/](evidence/upstream/README.md) | Original upstream claims with exact source/input associations; not scoring labels |
| [evidence/analysis/](evidence/analysis/README.md) | Current judgment evidence grouped by source batch and input |
| [taxonomy/](taxonomy/README.md) | Current five-category standard and classifications for all 90 negative inputs |
| `validation.json` | Input-bound compilation, extraction and preservation results; graphs are generated on demand |
| `provenance.json` | Source project bindings and archive locators |
| `materials/` | Independent-source acquisition locators and byte hashes |
| `support-inventory.json` | Current documentation, configuration, scripts and test hashes |
| `manifest.json` | Current publication SHA-256 inventory |
| `layout.json` | Exact compatibility aliases for embedded retained evidence locators |
| `release.json` | Source/documentation pins, active counts, and exclusions |

Upstream claims, our semantic judgment, and technical extraction evidence are
separate kinds of evidence. Compilation, proof completeness, and reference
readiness are also separate facts. See [the data contract](../docs/DATA-FORMAT.md).
The SLT batch remains excluded; see [the release scope](../docs/DATA-FORMAT.md#technical-states-and-limits).

The released Lean files are authoritative. Graphs, archived graph variants and
composition inputs are omitted; prior technical artifacts remain in Git history.

The two added Poincare source batches use the same root label, analysis,
validation and provenance paths as the original inputs. Their 26 annotation
records are explicitly preliminary, with unresolved judgments marked
`undetermined`. Compact context-check receipts are in `evidence/technical/`.
Only deferred plans and archive locators remain in each batch's metadata.
[Publication cleanup](poincare/publication-cleanup.json) records removed artifacts
and the preparation commit. The strict merge gate reports pending human labels
and historical-license scope separately.
