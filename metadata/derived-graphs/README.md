# Formal context graphs and technical evidence

| Path | Purpose |
| --- | --- |
| `retained-index.json` | Input/hash-bound access to all 171 context graphs |
| `index.json` | Current compilation/extraction receipts for all 171 statement contexts |
| `graphs/`, `retained/` | Retained historical and freshly extracted graph bytes |
| `receipts/<batch>/<id>.json` | Extraction and composition checks for named inputs |
| `components/stacks/` | Default/explicit graphs needed to verify the joint Stacks context |
| `composition-inputs/stacks/` | Two component source packages used solely for joint-context verification |

All 171 current graphs are freshly extracted from the released Lean contexts.
Receipts explicitly record proof erasure, source inventories, and preservation
checks for root statements and necessary non-proof definitions. Successful
extraction does not certify the omitted theorem proofs or semantic alignment.

Historical graphs and Stacks composition packages are retained as technical
provenance, outside active benchmark inputs. Embedded historical locators resolve
through `../layout.json`; current indexes use canonical graph/receipt paths.
