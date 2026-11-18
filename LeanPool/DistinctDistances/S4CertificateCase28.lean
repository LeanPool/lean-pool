/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase28Summary0
public import LeanPool.DistinctDistances.S4CertificateCase28Summary1

/-!
# Case 28 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case28Summary0.combine case28Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case28Build rows28 fullSummary := by
  rw [case28RowsShape]
  exact case28Summary0Checked.node case28Summary1Checked

/-- The case 28 certificate passes the original weighted-row checker. -/
theorem case28_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 28) (caseY.get 29)) rows28 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
