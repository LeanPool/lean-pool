/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase24Summary0
public import LeanPool.DistinctDistances.S4CertificateCase24Summary1

/-!
# Case 24 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case24Summary0.combine case24Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case24Build rows24 fullSummary := by
  rw [case24RowsShape]
  exact case24Summary0Checked.node case24Summary1Checked

/-- The case 24 certificate passes the original weighted-row checker. -/
theorem case24_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 24) (caseY.get 25)) rows24 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
