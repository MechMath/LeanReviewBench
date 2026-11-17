# Benchmark metadata

The release contains 171 versioned inputs across 16 batches, with 81 aligned and
90 misaligned provisional labels. Metadata are curator-facing and must remain
outside model-visible task exports.

| Path | Purpose |
| --- | --- |
| `labels/` | Binary verdicts, reasons, review states, and current analysis references |
| [evidence/upstream/](evidence/upstream/README.md) | Original upstream claims with exact source/input associations; not scoring labels |
| [evidence/analysis/](evidence/analysis/README.md) | Current judgment evidence grouped by source batch and input |
| [taxonomy/](taxonomy/README.md) | Current five-category standard and classifications for all 90 negative inputs |
| [derived-graphs/](derived-graphs/README.md) | Context graphs, extraction receipts, and composition validation inputs |
| `provenance.json` | Source project bindings and archive locators |
| `materials/` | Independent-source acquisition locators and byte hashes |
| `manifest.json` | Current publication SHA-256 inventory |
| `layout.json` | Exact compatibility aliases for embedded retained evidence locators |
| `release.json` | Source/documentation pins, active counts, and exclusions |

Upstream claims, our semantic judgment, and technical extraction evidence are
separate kinds of evidence. Compilation, proof completeness, and reference
readiness are also separate facts. See [the data contract](../docs/DATA-FORMAT.md).
The SLT batch remains excluded; see [the scope update](../docs/MIGRATION.md).
