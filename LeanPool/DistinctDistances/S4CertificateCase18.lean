/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase18Summary0
public import LeanPool.DistinctDistances.S4CertificateCase18Summary1

/-!
# Case 18 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case18Summary0.combine case18Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case18Build rows18 fullSummary := by
  rw [case18RowsShape]
  exact case18Summary0Checked.node case18Summary1Checked

/-- The case 18 certificate passes the original weighted-row checker. -/
theorem case18_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 18) (caseY.get 19)) rows18 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
