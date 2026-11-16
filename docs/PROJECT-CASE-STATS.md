# Registered project-case batch statistics

Generated from `datasets/project-cases.json`, registered project metadata and
`metadata/upstream-evidence/`. The tables below cover all registered batches.

Main contains **172 versioned inputs**
in **172 project directories**.

Reproduce: `python3 scripts/data/project_case_stats.py > docs/PROJECT-CASE-STATS.md`.
Machine-readable output: `python3 scripts/data/project_case_stats.py --json`.

`Roots` counts distinct declaration names within each repository; renamed
before/after declarations count separately. This is not a deduplicated count
of independent mathematical cases. `group_id` groups related inputs and can
also combine multiple mathematical roots, so it is not a case count either.
Provisional model reviews are retained separately in `metadata/labels/`.
Upstream statements are unverified claims,
including scope changes; linked inputs do not automatically inherit a verdict.

| Batch | Roots | Extracted roots | Inputs | Upstream records | Linked inputs | No retained evidence | Pairs |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| applied-modeling-lib | 26 | 20 | 30 | 0 | 0 | 30 | 6 |
| carleson | 5 | 5 | 7 | 1 | 2 | 5 | 2 |
| coarse-degiorgi | 7 | 6 | 7 | 2 | 4 | 3 | 0 |
| sphere-packing | 6 | 6 | 9 | 2 | 8 | 1 | 3 |
| formalslt | 4 | 4 | 6 | 2 | 4 | 2 | 2 |
| vaught | 3 | 3 | 3 | 3 | 3 | 0 | 1 |
| stat-learning-theory | 1 | 0 | 1 | 0 | 0 | 1 | 0 |
| statsmllib | 2 | 2 | 2 | 1 | 2 | 0 | 1 |
| brownian-motion | 1 | 1 | 2 | 0 | 0 | 2 | 1 |
| pfr | 14 | 14 | 24 | 10 | 22 | 2 | 11 |
| sphere-eversion | 4 | 4 | 6 | 2 | 4 | 2 | 3 |
| pnt | 21 | 21 | 40 | 11 | 40 | 0 | 19 |
| stacks | 6 | 6 | 5 | 0 | 0 | 5 | 1 |
| arklib | 7 | 7 | 12 | 0 | 0 | 12 | 5 |
| imperial-flt | 5 | 5 | 5 | 0 | 0 | 5 | 0 |
| equational-theories | 8 | 8 | 7 | 0 | 0 | 7 | 0 |
| apap | 2 | 2 | 6 | 0 | 0 | 6 | 3 |
| Total | 122 | 114 | 172 | 34 | 89 | 83 | 58 |

| Batch | Compiled/extracted inputs | Historical ready | Historical unresolved | Blocked | Both-extracted pairs |
| --- | ---: | ---: | ---: | ---: | ---: |
| applied-modeling-lib | 24 | 11 | 13 | 6 | 5 |
| carleson | 7 | 3 | 4 | 0 | 2 |
| coarse-degiorgi | 6 | 6 | 0 | 1 | 0 |
| sphere-packing | 9 | 9 | 0 | 0 | 3 |
| formalslt | 6 | 5 | 1 | 0 | 2 |
| vaught | 3 | 2 | 1 | 0 | 1 |
| stat-learning-theory | 0 | 0 | 0 | 1 | 0 |
| statsmllib | 2 | 0 | 2 | 0 | 1 |
| brownian-motion | 2 | 2 | 0 | 0 | 1 |
| pfr | 24 | 10 | 14 | 0 | 11 |
| sphere-eversion | 6 | 3 | 3 | 0 | 3 |
| pnt | 40 | 3 | 37 | 0 | 19 |
| stacks | 5 | 3 | 2 | 0 | 1 |
| arklib | 12 | 0 | 12 | 0 | 5 |
| imperial-flt | 5 | 0 | 5 | 0 | 0 |
| equational-theories | 7 | 0 | 7 | 0 | 0 |
| apap | 6 | 0 | 6 | 0 | 3 |
| Total | 164 | 57 | 107 | 8 | 57 |

The 58 explicit reciprocal before/after links cover 116 inputs;
56 inputs have no registered pair. Pairs include text-only revisions,
renamed declarations and scope changes; after does not imply a successful repair.

Historical status values use `historical_status` where a review updated `status`. In particular,
`ready` formerly included a provisional model decision; it is not a current scoring
or semantic approval. Use the compilation/extraction flags for technical counts.
No retained upstream evidence means this pass kept no sufficiently explicit statement;
it does not establish that none exists anywhere upstream.
