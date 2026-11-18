/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4CertificateCase19Summary0
public import LeanPool.DistinctDistances.S4CertificateCase19Summary1

/-!
# Case 19 of the `1/40` certificate
-/

@[expose] public section

namespace Esgk.S4

open FarkasPackedCheck

private noncomputable def fullSummary : PackedSummary :=
  case19Summary0.combine case19Summary1

private theorem fullSummaryChecked :
    SummaryValid 256 params.box case19Build rows19 fullSummary := by
  rw [case19RowsShape]
  exact case19Summary0Checked.node case19Summary1Checked

/-- The case 19 certificate passes the original weighted-row checker. -/
theorem case19_check : FarkasPackedCheck.check 256 params.box
    (params.buildInt (caseY.get 19) (caseY.get 20)) rows19 = true :=
  fullSummaryChecked.checked (by decide +kernel)

end Esgk.S4
