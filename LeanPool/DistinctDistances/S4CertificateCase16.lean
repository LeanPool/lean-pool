/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase16Summary0
public import LeanPool.DistinctDistances.S4CertificateCase16Summary1

/-!
# Case 16 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case16Summary0.combine case16Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case16Build rows16 fullSummary := by
  rw [case16RowsShape]
  exact case16Summary0Checked.node case16Summary1Checked

/-- The case 16 certificate passes the original weighted-row checker. -/
theorem case16_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 16) (caseY.get 17)) rows16 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
