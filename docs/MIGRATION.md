# Local release migration

This preview is derived from the clean research integration snapshot `18086147ad0f8bcac09485289aeda217747de2f6`. It creates a separate local repository; it does not rewrite the research repository, its history, or its remote branches. No release remote has been configured. Complete uncompressed data is included in the local Git repository.

## Retained collection

| Item | Result |
| --- | ---: |
| Active inputs | 172 |
| Collection batches | 17 |
| Unique normalized declaration contexts | 159 |
| Provisional aligned labels | 82 |
| Provisional misaligned labels | 90 |
| Human gold / `reference_ready=true` labels | 0 |
| Exact formal source/resource files retained | 8,734 |
| Inputs marked compiled in the original source | 164 |
| Historically blocked full compilation, with recovered exported contexts | 8 |

The 30 inputs from ArkLib, Imperial FLT, Equational Theories and APAP are retained. The five previously excluded repositories and the four high-cost ArkLib Binius/Hachi inputs remain outside the active collection. Stacks `STK-0B34` retains the refactor layout: one input with two roots. The historical independent left/right records and their newer labels remain archived in the research history, not additional release tasks. Sheffer also retains its joint-input layout.

The [catalog](../releases/0.1.0-preview/catalog.csv) maps opaque release task IDs to research identities. The manifest records each input batch and its count. Original labels, review state and input digests are preserved in the references directory, while normalized release payloads have separate content hashes. Normalization removes graph metadata such as docstrings and source locations; it does not rewrite the selected independent mathematical text, declaration types or retained definition values.

## Storage layout

The research checkout previously contained 58,886 tracked files totaling approximately 1,437.9 MiB of file contents. This measurement is the tracked checkout content, not compressed Git storage or clone transfer size. The new repository tracks about 1 MiB of code, documentation and inventories plus the complete uncompressed dataset, with no imported research history.

| Git-tracked data directory | Files | Bytes | Approximate MiB |
| --- | ---: | ---: | ---: |
| `inputs/` | 160 | 43,111,014 | 41.11 |
| `references/` | 131 | 8,052,183 | 7.68 |
| `reproduction/` | 3,438 | 94,970,927 | 90.57 |
| Total | 3,729 | 146,134,124 | 139.36 |

The earlier packaging prototype compressed these same data bytes into 18.76 MiB of archives. Following the decision to keep the release directly readable, the archives and extraction workflow have been removed from the release. A fresh clone can immediately load, validate and score the dataset. Git handles its own storage compression.

Only one canonical graph representation is retained per unique context. Source files are deduplicated by their byte hash, with original paths recorded in `projects.jsonl`. Research logs, excluded candidates, experiment outputs, build caches and repeated graph encodings are omitted. Only scratch versions, run outputs and materialized build/source trees remain ignored.

## Validation performed

The [verification record](../releases/0.1.0-preview/verification.json) records a complete comparison against the pinned research snapshot:

- All 172 original labels and selected independent informal texts are unchanged.
- Every released context matches the canonical normalization of its original exported graph, including contexts recovered from pinned archive Git objects.
- All 8,734 retained formal source/resource files match their original bytes.
- All 172 task payloads pass loader validation; input-only loading succeeds without accessing references or the research checkout.
- All 12 tests pass, covering malformed/tampered payloads, reference bindings, provisional scoring, file inventory checks, joint-input layouts and exact source/resource restoration.
- Rebuilding all three data directories from the same source produces identical file inventories and SHA-256 hashes; see the [determinism record](../releases/0.1.0-preview/determinism.json).

A constant-prediction submission was used only to exercise the scoring interface. It is not a model evaluation result. No Lean recompilation was performed as part of this packaging migration: the original compilation flags and evidence are retained, and recovered context availability does not imply successful full-project compilation.

## Conditions before a public gold release

All labels retain `reference_ready=false`. Review reports and existing user confirmations are preserved without upgrading them to human-adjudicated gold labels. Three legacy label records have empty reasons; these historical records remain unchanged, while new predictions must supply a nonempty reason.

The two KZG function-binding inputs retain dated cached CGKY25 text, but the precise original PDF revision and its hash are still unverified. Evidence and locator caveats are available in evaluator provenance. The historical AppliedModelingLib license-copy gap remains documented in the license index; upstream attribution and redistribution terms require their own review before public redistribution.

A final human review policy and official evaluation splits are not defined by this preview. These are publication decisions still to be completed. Separate artifact hosting and download URLs are unnecessary for the Git-tracked dataset. Local input loading, development scoring and source restoration are already usable without network access or the research repository.
