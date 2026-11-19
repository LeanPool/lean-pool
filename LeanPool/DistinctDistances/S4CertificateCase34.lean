/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase34Summary0
public import LeanPool.DistinctDistances.S4CertificateCase34Summary1

/-!
# Case 34 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case34Summary0.combine case34Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case34Build rows34 fullSummary := by
  rw [case34RowsShape]
  exact case34Summary0Checked.node case34Summary1Checked

/-- The case 34 certificate passes the original weighted-row checker. -/
theorem case34_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 34) (caseY.get 35)) rows34 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
