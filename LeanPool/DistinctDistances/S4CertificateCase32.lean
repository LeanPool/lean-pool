/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase32Summary0
public import LeanPool.DistinctDistances.S4CertificateCase32Summary1

/-!
# Case 32 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case32Summary0.combine case32Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case32Build rows32 fullSummary := by
  rw [case32RowsShape]
  exact case32Summary0Checked.node case32Summary1Checked

/-- The case 32 certificate passes the original weighted-row checker. -/
theorem case32_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 32) (caseY.get 33)) rows32 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
