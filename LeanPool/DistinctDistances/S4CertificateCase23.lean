/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase23Summary0
public import LeanPool.DistinctDistances.S4CertificateCase23Summary1

/-!
# Case 23 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case23Summary0.combine case23Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case23Build rows23 fullSummary := by
  rw [case23RowsShape]
  exact case23Summary0Checked.node case23Summary1Checked

/-- The case 23 certificate passes the original weighted-row checker. -/
theorem case23_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 23) (caseY.get 24)) rows23 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
