/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase30Summary0
public import LeanPool.DistinctDistances.S4CertificateCase30Summary1

/-!
# Case 30 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case30Summary0.combine case30Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case30Build rows30 fullSummary := by
  rw [case30RowsShape]
  exact case30Summary0Checked.node case30Summary1Checked

/-- The case 30 certificate passes the original weighted-row checker. -/
theorem case30_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 30) (caseY.get 31)) rows30 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
