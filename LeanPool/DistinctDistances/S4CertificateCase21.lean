/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase21Summary0
public import LeanPool.DistinctDistances.S4CertificateCase21Summary1

/-!
# Case 21 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case21Summary0.combine case21Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case21Build rows21 fullSummary := by
  rw [case21RowsShape]
  exact case21Summary0Checked.node case21Summary1Checked

/-- The case 21 certificate passes the original weighted-row checker. -/
theorem case21_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 21) (caseY.get 22)) rows21 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
