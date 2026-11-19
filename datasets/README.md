# Released project inputs

The dataset contains **171 inputs across 16 batches**, with 81 aligned and
90 misaligned human judgments. The registry is
[project-cases.json](project-cases.json); see [statistics](../docs/STATISTICS.md)
for per-batch counts and counting conventions.

```text
datasets/
  project-cases.json
  <batch>/
    README.md
    index.csv
    projects/<id>/
      project.json
      informal.jsonl
      CHANGES.md
      formal/
        Main.lean
        dep/
```

Each `project.json` records the upstream repository and commit, selected roots,
version relationships, pinned environment, file inventory and input hashes.
`informal.jsonl` preserves the independently sourced target and its root bindings.
`CHANGES.md` briefly records Lean migration changes.

The Lean files retain the roots' declaration contexts and the notation,
instances and other support needed to elaborate them. Proof bodies are replaced
with `sorry`; non-proof definition values are preserved. All 171 contexts have
recorded compilation and graph-extraction checks in `metadata/validation.json`. These checks validate the
statement contexts and do not certify the original proofs.

Human judgments, taxonomy assignments and source evidence are stored separately
under `metadata/` and are excluded from model-visible inputs. Input hashes bind
annotations and validation records to the current packaged sources. Dependency
graphs are generated on demand from Lean and are not distributed. See the
[data contract](../docs/DATA-FORMAT.md) and
[construction method](../docs/CONSTRUCTION.md).

```sh
python3 scripts/data/check_release_candidate.py
python3 scripts/data/project_case_stats.py --json
```

The evaluation protocol is tracked in
[issue #1](https://github.com/MechMath/LeanReviewBench/issues/1).

Two further batches use the same native dataset layout and await human review:
[qinz1yang](qinz1yang/README.md) (15 inputs) and
[FrenzyMath](frenzymath/README.md) (11 inputs). All 26 are complete declaration
contexts; three technically deferred contexts and five excluded development
artifacts have been removed. Their plans and pinned Git archive locators remain
in batch metadata. One historical pair has identical input content and shares
its split/group, yielding 25 distinct contexts. Together with the original
171 human-reviewed inputs, the native loader reads 197 retained inputs.

Labels, analysis, context-validation evidence, provenance and license records
use the same root metadata locations as the existing batches. Run
`python3 scripts/data/check_release_candidate.py --require-reviewed` for the
strict merge gate: preliminary labels do not satisfy human review, and labels
do not resolve a historical-license gap.
