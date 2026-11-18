/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase22Summary0
public import LeanPool.DistinctDistances.S4CertificateCase22Summary1

/-!
# Case 22 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case22Summary0.combine case22Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case22Build rows22 fullSummary := by
  rw [case22RowsShape]
  exact case22Summary0Checked.node case22Summary1Checked

/-- The case 22 certificate passes the original weighted-row checker. -/
theorem case22_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 22) (caseY.get 23)) rows22 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
