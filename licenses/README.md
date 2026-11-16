# Source licenses and attribution

This directory covers the thirteen retained project-case batches and identified
third-party source material in their local closures. Names match dataset names.
License bundles for the removed OpenAI/OAI, FLT and Kakeya datasets remain with
their data in the `11_9_shenhao` archive branch.
The repository-level [LICENSE](../LICENSE) does not override upstream terms.

| Batch | Software license | Retained evidence |
| --- | --- | --- |
| applied-modeling-lib | Current upstream declares Apache-2.0 | [Historical copy pending](applied-modeling-lib/README.md) |
| carleson | Apache-2.0 | [License copy](carleson/LICENSE) |
| coarse-degiorgi | Apache-2.0 | [License copy](coarse-degiorgi/LICENSE) |
| sphere-packing | Apache-2.0 | [License copy](sphere-packing/LICENSE) |
| formalslt | MIT | [License copy and copyright](formalslt/LICENSE) |
| vaught | Apache-2.0 | [License copy](vaught/LICENSE) |
| statsmllib | Apache-2.0 | [License copy](statsmllib/LICENSE) |
| brownian-motion | Apache-2.0 | [License copy](brownian-motion/LICENSE) |
| pfr | Apache-2.0 | [License copy](pfr/LICENSE) |
| sphere-eversion | Apache-2.0 | [License copy](sphere-eversion/LICENSE) |
| pnt | Apache-2.0 | [License copy](pnt/LICENSE) |

Additional retained sources require [add-combi](add-combi/LICENSE),
[CoarseGraining](coarse-graining/LICENSE), [Mathlib](mathlib/LICENSE), and
[IEANTN](ieantn/LICENSE) notices. IEANTN documentation supplies the four newly
bound Vinogradov informal targets in the PNT batch.
In particular, the two energy inputs in the PFR batch actually originate in
leanprover-community/add-combi. Homogenization helpers in coarse-degiorgi come
from CoarseGraining. Mathlib-derived helpers retain their original per-file
notices; importing an external library does not mean its full sources are bundled.

[index.json](index.json) records exact candidate source revisions, retained
license hashes and the immutable source/archive used for each copy. Archived
copies and current upstream policy are distinguished. A retained repository
license is not a new per-file or historical licensing adjudication.

Original copyright and author headers in Lean sources remain authoritative.
License texts are retained without normalization. Source-paper excerpts,
blueprints, figures and other third-party materials keep their own terms;
software license entries do not automatically license those materials.

The candidate checker validates index coverage, source revisions and license
file hashes. It preserves the AppliedModelingLib historical-copy gap rather
than treating a successful integrity check as redistribution clearance.
