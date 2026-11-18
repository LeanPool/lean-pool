/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase14Summary0
public import LeanPool.DistinctDistances.S4CertificateCase14Summary1

/-!
# Case 14 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case14Summary0.combine case14Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case14Build rows14 fullSummary := by
  rw [case14RowsShape]
  exact case14Summary0Checked.node case14Summary1Checked

/-- The case 14 certificate passes the original weighted-row checker. -/
theorem case14_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 14) (caseY.get 15)) rows14 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
