# Benchmark metadata

The registered inventory contains 171 project-case inputs across 16 batches. Labels and source/review metadata are outside model-visible task exports.

| Path | Purpose |
| --- | --- |
| `labels/` | Original input-bound provisional binary records and review state |
| `upstream-evidence/` | Explicit upstream excerpts and exact source/input bindings; not labels |
| `derived-graphs/index.json` | Original recovered graph bindings and receipts |
| `derived-graphs/retained-index.json` | Local hash-bound access to every active input's original exported graph |
| `provenance.json` | Original project bindings and archive locators |
| `manifest.json` | Native publication SHA-256 inventory |
| `reports/` | Review reports and graph/composition evidence |
| `taxonomy/` | Five-category standard, provisional classifications, summaries, and evidence provenance |
| `layout.json` | Prefix aliases that preserve original hash-bound evidence references |
| `release.json` | Source/documentation commit pins, active counts and packaging exclusions |

Historical `reports/...` paths not retained locally remain archive locators, resolvable with `scripts/data/provenance.py`. All currently hashed review reports required by the label audit are retained at their original paths. Compiled contexts, recovered contexts, proof completeness and semantic reference readiness are separate facts. See [the contract](../docs/DATA-FORMAT.md).

Runtime evidence is consolidated in `metadata/reports/`. Fields in original records still use `reports/...`; `scripts/data/paths.py` resolves them without changing any record bytes or evidence hash. The former `references/` directory contained only a redundant guide; authoritative provisional labels remain in `metadata/labels/`.

The [misalignment taxonomy](taxonomy/README.md) groups the standard and diagnostic
classifications outside binary label records and model-visible inputs. All 90 current negative inputs have provisional diagnostic labels bound to the
current standard and input hashes. Classification dates and retained source
evidence are recorded per input; prior versions remain in Git.

The SLT batch was excluded by curator decision; see [the scope update](../docs/MIGRATION.md).
