# Packaging changes

STK-0B34-left and STK-0B34-right were merged into STK-0B34 on 2026-11-12 at the user's request. Both declarations jointly bind the same source informal statement.

Main.lean is byte-identical to both predecessor inputs and the pinned upstream source. The existing proof holes are preserved. The input hash changes because the target binding changes.

Default and explicit graphs are exact unions of the two retained component graphs. Their original Lean 4.34.1 compilation evidence is reused for unchanged formal sources; no new Lean compilation or proof certification is claimed. See reports/stacks-admission/technical/STK-0B34/receipt.json and reports/stacks-admission/merges/STK-0B34.json.
