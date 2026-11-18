/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase15Summary0
public import LeanPool.DistinctDistances.S4CertificateCase15Summary1

/-!
# Case 15 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case15Summary0.combine case15Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case15Build rows15 fullSummary := by
  rw [case15RowsShape]
  exact case15Summary0Checked.node case15Summary1Checked

/-- The case 15 certificate passes the original weighted-row checker. -/
theorem case15_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 15) (caseY.get 16)) rows15 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
