/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase13Summary0
public import LeanPool.DistinctDistances.S4CertificateCase13Summary1

/-!
# Case 13 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case13Summary0.combine case13Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case13Build rows13 fullSummary := by
  rw [case13RowsShape]
  exact case13Summary0Checked.node case13Summary1Checked

/-- The case 13 certificate passes the original weighted-row checker. -/
theorem case13_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 13) (caseY.get 14)) rows13 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
