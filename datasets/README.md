# project-case publication candidate

Current integration scope: **172 inputs across 17 batches**, with 172 binary labels (82 aligned, 90 misaligned). Stacks retains refactor’s joint STK-0B34 input; the two research component inputs and their newer labels are archived. The four newly extracted repositories retain all 30 inputs and their current labels. Older counts below describe dated baseline history.

The original reviewed baseline contains **13 datasets and 143 versioned inputs**.
The current branch additionally registers 30 snapshots from the four retained handoff repositories
(ArkLib, Imperial FLT, Equational Theories, APAP); see [extraction results](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/pending-extraction-2026-11-13/README.md).
All current batches are registered in
[project-cases.json](project-cases.json), indexed by CSV, with reviewed labels
in `metadata/labels/`. OpenAI, Kakeya and FLT and their frozen release manifest
are excluded; the complete previous main is preserved on branch `11_9_shenhao`
at commit `07e36bb64b0cff457694cfe9f1e156a3966a0dbc`.

There are 143 versioned inputs, 100 repository/root declaration names (92 extracted)
and 50 before/after pairs. See [statistics](../docs/PROJECT-CASE-STATS.md)
for per-batch counts and counting limits. Retained blocked or undetermined inputs
are not automatically eligible evaluation tasks.

```text
datasets/
  project-cases.json
  <batch>/
    README.md
    index.csv
    projects/<id>/
      project.json
      informal.jsonl
      formal/
        Main.lean
        dep/
```

Project metadata records source pin, selected root, file inventory, input hashes,
family splits, reciprocal version links, technical status and provenance.
Informal records retain exact source text and target bindings; missing complete
targets are disclosed. Formal closures retain definition values and historical
proof holes. Explicit upstream statements live outside inputs in
`metadata/upstream-evidence/`. Provisional review labels for 143 inputs are in
`metadata/labels/`, outside model-visible task exports; no gold labels are supplied.

Project input bytes are unchanged by metadata cleanup. Historical
report paths resolve through [provenance metadata](../metadata/README.md).

```sh
python3 scripts/data/check_release_candidate.py
python3 scripts/data/project_case_stats.py --json
```

The registered batches use CSV indexes. Their evaluation export and reference
binding still need separate preparation before using the frozen-package runner.
See [maintenance](../docs/PROJECT-CASE-WORKFLOW.md).

Historical staging remains in [the staging batch](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/datasets/staging/real-repairs-2026-11-12/README.md).
The new formal packages record fresh compilation and graph extraction after relocation.
Unreviewed inputs remain ineligible for evaluation and have no assigned binary reference label.
