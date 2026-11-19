/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase29Summary0
public import LeanPool.DistinctDistances.S4CertificateCase29Summary1

/-!
# Case 29 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case29Summary0.combine case29Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case29Build rows29 fullSummary := by
  rw [case29RowsShape]
  exact case29Summary0Checked.node case29Summary1Checked

/-- The case 29 certificate passes the original weighted-row checker. -/
theorem case29_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 29) (caseY.get 30)) rows29 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
