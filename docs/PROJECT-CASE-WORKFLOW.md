# Real-project case maintenance

Current annotation format: all 171 binary labels are human reviewed. JSONL records
retain current results only, with concise English reasons/scopes. Analysis paths
and hashes are maintained in the evidence index; dated descriptions below refer
to earlier preparation stages.

Current integration scope: **171 inputs across 16 batches**, with 171 binary labels (81 aligned, 90 misaligned). Stacks retains refactor’s joint STK-0B34 input; the two research component inputs and their newer labels are archived. The four newly extracted repositories retain all 30 inputs and their current labels. Older counts below describe dated baseline history.

The original thirteen batches registered in [project-cases.json](../datasets/project-cases.json)
contain 143 versioned inputs, 100 repository/root declaration names (92 with
extracted snapshots) and 50 before/after pairs. These are not independent
mathematical-case counts. See the [generated statistics](PROJECT-CASE-STATS.md)
and [construction procedure](CONSTRUCTION.md).

## Files and responsibilities

```text
datasets/<repo>/
  README.md
  index.csv
  projects/<case-id>/
    project.json
    informal.jsonl
    CHANGES.md             # When compatibility edits exist
    formal/
      Main.lean
      dep/                 # Transitive repository-local imports
metadata/evidence/upstream/
```

`project.json` records upstream repository, full commit, original root/module,
source URL/hash, discovery links, target mapping, historical status, version
relationships, split identity and provenance. `index.csv` is generated from it.
Keep the selected Formal semantics and input hashes unchanged during metadata
cleanup. A project is one retained snapshot, including blocked candidates.

`informal.jsonl` contains frozen paper/blueprint text or a specification with
source locators and scope notes. A scope note is not an independent quotation.
Four PNT inputs have empty informal records, null `informal_id` and
`evaluation_eligible: false`; do not invent a target for them.
Two KLN inputs gained checked paper targets on 2026-11-09; their input hashes,
review bindings and provenance were updated explicitly.

`formal/Main.lean` and `formal/dep/` retain local statement and definition context,
proof source and historical proof holes. Mathlib and Cslib remain external.
`CHANGES.md` records compatibility changes against the selected snapshot;
these changes are distinct from upstream before/after repairs. No new all-case
compilation or semantic approval follows from static checks.

## Evidence and labels

Only explicit upstream statements are retained in
[upstream-evidence](../metadata/evidence/upstream/README.md). Each excerpt keeps
its original source field, archive locator and links to current input hashes.
Association notes are curator explanations, not upstream quotes. Version links
do not assert that the upstream claim holds for each linked snapshot.

The restored 2026-11-05 provisional reviews for the original four batches and
subsequent updates live in `metadata/labels/`, with current evidence under `metadata/evidence/analysis/`.
Those dated reviews cover the original 137 inputs: 70 misaligned and 67 aligned, with none undetermined.
The other eight batches' 84 records were restored from `d6a463a1` on 2026-11-09
after matching exact input hashes and roots. Their reasons remain unchanged;
this migration alone was not a new semantic adjudication. A subsequent parallel
review resolved 47 of 60 pending cases, with all old records retained in
`reports/pre-qwen-review-2026-11-09/`. A further review resolved 9 of those 13
remaining cases, including four new independent target bindings, recorded in
`reports/undetermined-review-2026-11-09/`. The final four Vinogradov targets were
newly bound to later IEANTN documentation, with two aligned and two misaligned;
see `reports/vinogradov-target-search-2026-11-09/`. All original 137 binary labels can be
used for provisional reference-agreement scoring against their current input hashes.
Earlier evaluation snapshots retain their original inputs and labels.
The upstream statements themselves are unverified and may include deliberate
restrictions, open assumptions or AI-generated reports. They are not scoring
references for the evaluation tools.

Source links, upstream evidence, compatibility notes and version relationships
must stay outside a future model-visible task export. That export also needs
appropriate comment/proof filtering and its own release and labeling contract.
The existing package exporters do not directly consume project-case inputs.

## Versions and historical status

Before/after projects have reciprocal IDs and shared `group_id` / `split_group`.
All related repository versions remain in the same split. There are 50 pairs;
ordering does not establish a successful repair. Declaration names and group
IDs are not independent case counts.

Reviewed projects preserve their original status in `historical_status`. Current
`status` is `misaligned` for confirmed negative reviews and `undetermined` for
unresolved reviews. Positive reviews use `label: aligned` and retain/use `status: ready`
when the existing technical requirements for ready are met.
`alignment_reference` points to the exact hash-bound review.
`technical_status` separately records extracted/blocked availability.
The preserved historical status vocabulary is:

- `ready`: historically compiled/extracted with a provisional model decision.
- `undetermined`: historically unresolved informal scope or correspondence.
- `blocked`: incomplete technical extraction or missing necessary pairing.

These historical fields no longer imply an available label. Use
`compiled_lean434`, `leantrace_extracted`, `packaged_compilation`,
`missing_modules` and `evaluation_eligible` to inspect technical and input
availability. Even a compiled project may lack an independent informal target.

## External environment and checks

Lean, Mathlib, Cslib and extraction tools use the explicit external configuration
documented in [ENVIRONMENT.md](ENVIRONMENT.md). To inspect or compile:

```sh
python3 scripts/construction/compile_projects.py env
python3 scripts/construction/compile_projects.py compile --dataset carleson --ids CAR-01-before
```

Build outputs stay under `build/`. Static maintenance needs only Python:

```sh
python3 scripts/data/project_cases.py index
python3 scripts/data/check_release_candidate.py
python3 scripts/data/project_case_stats.py > docs/PROJECT-CASE-STATS.md
python3 scripts/data/upstream_evidence.py --archives
```

The last command optionally checks excerpts against historical Git objects;
ordinary candidate validation does not require archive access. Input edits
require deliberate provenance updates. A manifest refresh cannot approve a
semantic change or manufacture a reference label.

Screen new repositories one branch at a time, freeze source revisions and
independent informal targets, preserve Formal semantics during compatibility
repairs, and extract against pinned external libraries. Retain upstream claims
only when explicit; skip generic leads rather than supplying a model verdict.
Full construction recipes, graphs, logs and unsuccessful attempts remain in
the historical archive. `scripts/data/provenance.py --path <original-path>`
resolves historical `reports/...` locators to immutable URLs.

Stacks admission adds six technically extracted inputs: two provisionally aligned, one misaligned and three unresolved scopes. See [admission](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/stacks-admission/README.md). Earlier dated 137-input review summaries above remain historical; current totals are generated in PROJECT-CASE-STATS.md.

The 2026-11-13 extraction branch adds explicitly registered packages with separate technical receipts and unresolved human scope review. See [current extraction results](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/pending-extraction-2026-11-13/README.md) and regenerated statistics for current totals.


The merge format and review/reference-state distinctions are specified in [DATA-FORMAT.md](DATA-FORMAT.md). The latest research label coverage and baseline merge preflight are recorded in [the 2026-11-16 audit](https://github.com/MechMath/PaperLeanBench/blob/18086147ad0f8bcac09485289aeda217747de2f6/reports/merge-readiness-2026-11-16/README.md).
