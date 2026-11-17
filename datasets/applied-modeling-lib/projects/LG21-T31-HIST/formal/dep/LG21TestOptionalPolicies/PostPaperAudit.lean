import Mathlib

import dep.LG21TestOptionalPolicies.ProofInterface

/-!
# Post-paper audit: Test-optional Policies

This file is the importable audit ledger for
*Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*.

`PaperInterface.lean` is the compact human-facing statement surface.  It exposes
only the named paper definitions and results.  This ledger imports the broader
implementation-facing `ProofInterface.lean` and gives source-numbered audit
entrypoints for the paper definitions, named results, proof-route variants, and
diagnostic scope checks.

The paper-facing Section 3 and Section 4 source-model routes are closed.  The
extra raw arbitrary-policy and pointwise-boundary diagnostics recorded here are
scope checks for overbroad abstractions, not caveats on the paper statements.
-/

namespace LG21TestOptionalPolicies

namespace PostPaperAudit

/- Audit endpoint for the Section 3 hidden-access information-set assumption. -/
abbrev audit_theorem3_1_section3_optional_reporting :=
  @paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding

/- Audit endpoint for Theorem 3.1, report-required Section 3 branch. -/
end PostPaperAudit

end LG21TestOptionalPolicies
