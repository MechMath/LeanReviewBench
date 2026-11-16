# Publication dependency policy

The release includes what is needed to inspect the current benchmark, validate its integrity and labels, run offline regression tests, and use the retained evaluation tools with supplied task packages. It does not reproduce the entire benchmark construction workspace.

| Keep locally | Reason |
| --- | --- |
| Registered `project.json`, full `informal.jsonl`, formal Lean sources and runtime resources | Actual benchmark inputs and native input hashes |
| Referenced `CHANGES.md` | Native package contract and compatibility notes |
| Common Lean/library pins and external tool configuration | Optional compilation environment |
| One exact retained dependency graph per exported context | Local access to all 172 inputs' formal meaning |
| Native labels, upstream evidence and source/license attribution | Label bindings and required provenance |
| Currently hashed review reports and derived/composed graph evidence | Files actually consumed by current validators |
| Protocol schemas, provider templates, runtime scripts and relevant upstream tests | Offline tool operation and regression coverage |
| Current docs and support-file inventory | Usable, auditable checkout |

Historical source clones under `original/`, duplicate original tarballs, patches, compilation logs, optional paper/website caches, unbound old review reports, screening attempts, excluded candidates and experiment outputs are omitted. They do not participate in the preserved input digest or current runtime checks. Historical references use immutable source commit URLs; no original label, informal record, project metadata or formal source is changed to achieve this cleanup.

`metadata/materials/index.json` records independent-source attachment locators and byte hashes, with pinned archive URLs instead of copying those optional acquisition materials. The independently supplied mathematical text remains verbatim in each `informal.jsonl`. Archive-only source material is not a dependency of local validation or offline tests, and its archival availability does not establish exact original PDF version or mathematical adequacy.

`reports/` contains only current hashed review reports and evidence required by the derived/composed graph checks. Archived Stacks component inputs remain there solely because the joint-graph validator consumes them; they are not active tasks. Other historical report links are fixed commit URLs.

The native project-case collection still requires a deliberate filtered model task export and export-bound reference review before official scoring. The retained protocol tests use temporary packages and mocked provider calls. Passing those tests does not create gold labels or demonstrate model accuracy.

## Checks and maintenance

```sh
python3 tools/check_support_files.py
python3 scripts/data/check_release_candidate.py
python3 scripts/data/annotation_coverage.py
python3 -m unittest discover -s tests -v
```

`metadata/manifest.json` covers native data/metadata/license bytes. `docs/support-inventory.json` additionally covers docs, configurations, scripts, tests and release helpers. After reviewing an intentional support-file edit, refresh that inventory with `python3 tools/check_support_files.py --freeze`; this does not approve an input or label change. Historical documentation links are pinned to the source repository; runtime needs no network or research checkout.
