# Native-format release migration

The active data come from integration commit `18086147ad0f8bcac09485289aeda217747de2f6`. The remote research documentation was fetched and checked at `2f471585a4b71adb32f6e3fac214e366ce8979ae`. The [paper construction appendix](source-contracts/paper/app_imple_detail.tex), [pinned research workflow](source-contracts/research/PROJECT-CASE-WORKFLOW.md) and current integrated [DATA-FORMAT.md](DATA-FORMAT.md) establish the native project-case contract. Dated counts in historical documents do not override the registered active inventory.

## Restored contract

The release now uses `datasets/<batch>/projects/<id>/project.json`, complete `informal.jsonl`, directly readable `formal/Main.lean` and `formal/dep/`, and per-batch `index.csv`. It retains `paperlean-project-case-1`, original stable project IDs, environment pins, target mappings, scope/source records, version links and the original digest schemes.

Labels return to `metadata/labels/<batch>.jsonl`; upstream evidence, provenance, license records, recovered graph bindings and the publication manifest use the original native schemas and paths. Current hashed review reports remain at their original report paths. Referenced compatibility notes and validator-required evidence are retained; other construction history is linked to fixed archive commits.

The earlier release-only input/context schemas, centralized task table, source blobs, archive installer, custom prediction/scoring interface and `data/0.1.0-preview` tree have been removed. They are not the published contract. All required local input and evidence files are uncompressed and tracked by Git. Optional acquisition materials are represented by pinned archive locators. Git history has not been rewritten.

## Retained inventory

| Item | Result |
| --- | ---: |
| Active inputs / registered batches | 172 / 17 |
| Aligned / misaligned provisional labels | 82 / 90 |
| Reference-ready labels | 0 |
| Formal source/resource files across active packages | 8,734 |
| Exact original graph bindings available locally | 172 |
| Inputs marked compiled in the original source | 164 |
| Historically blocked full compilation, with recovered contexts | 8 |

The 30 ArkLib, Imperial FLT, Equational Theories and APAP inputs remain. The five excluded repositories and four high-cost Binius/Hachi inputs remain excluded. Stacks `STK-0B34` remains one joint two-root input, as previously agreed; its archived component evidence remains under reports, outside active input counts. Equational Sheffer also remains one two-root input.

| Current tracked data tree | Files | File-content bytes | MiB |
| --- | ---: | ---: | ---: |
| `datasets/` | 9,265 | 192,154,028 | 183.25 |
| `metadata/` | 193 | 69,603,567 | 66.38 |
| `reports/` | 69 | 437,120 | 0.42 |
| `licenses/` | 24 | 255,547 | 0.24 |

These are uncompressed checkout file-content sizes, not clone transfer or compressed Git storage. Restoring ordinary per-project source paths repeats shared imports across packages, so this layout is larger than the earlier deduplicated 139.36 MiB prototype. It remains much smaller than the research checkout's approximately 1,437.9 MiB / 58,886 tracked files. Per-declaration graph files, repeated graph encodings, experiment outputs, staging/excluded candidates and build caches remain omitted. The final test-focused selection also omits expanded `original/` source clones, patches, build logs and optional source acquisition caches; see [PACKAGING.md](PACKAGING.md).

## Verification

The [byte comparison](migration-verification.json) confirms that all active `project.json` files, complete informal records, original label files, 8,734 source/resource files and retained original graph bytes match the pinned research snapshot. Input digests are checked using the original `project_cases.input_digest`, including the two established multi-root schemes and non-Lean runtime resources.

The original `check_release_candidate.py` passes: registered scope, indexes, hashes, labels, 13 derived graph/receipt bindings, 34 upstream evidence records, provenance and licensing inventory. The annotation coverage audit passes with 172 binary labels and zero reference-ready records. The release and upstream regression tests cover native metadata preservation, changed Lean/resource rejection, graph hashes/input bindings, unsafe paths, joint roots and complete publication integrity. A fresh-clone check needs no research checkout, archive download or data preparation. The test-focused layout was rebuilt into a fresh directory; its native inventory matches byte-for-byte and its support-file audit passes. See [the rebuild record](rebuild-verification.json).

`metadata/derived-graphs/retained-index.json` adds local access to the original graphs for every active input without changing original project metadata. It records source commit/path/hash and explicitly marks this migration as not performing a fresh build. Original derived records and composition evidence retain their original validation paths.

## Evaluation and remaining limits

This restores the latest native data contract, not a newly frozen model export. Package metadata and source modules include history, comments and proofs, and must not be copied wholesale into prompts. The original protocol tools remain available for separately supplied complete evaluation packages, exactly as upstream documented; a native conversion and its exact reference bindings are still separate work. The current native dataset has binary labels; older transport abstention is not a third gold class.

All labels remain provisional. Three legacy aligned labels have empty reasons; no justifications have been invented. The two KZG function-binding inputs still lack a verified exact original PDF revision/hash. The AppliedModelingLib historical license-copy gap remains recorded. No Lean recompilation, proof completeness certification or semantic re-annotation is claimed by this migration. The original research checkout and remote data branches remain unchanged apart from read-only remote reference fetching; no release push has been performed.
